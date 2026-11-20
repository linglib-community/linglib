module

public import Studies.PlebaniRosellaSaitta2022

/-!
# Champollion and Bernard (2024): Negation and modality in unilateral truthmaker semantics

Events form a complete lattice with a primitive exclusion relation `excl`. Two events conflict
when a part of one excludes a part of the other, an event is possible when it does not conflict
with itself, and a world is a maximal possible event (`Truthmaker.Conflict`,
`Truthmaker.possible`). An event verifies the negation of a proposition `φ` when it is a fusion
$\bigsqcup_{f \in φ} h(f)$ in which each $h(f)$ excludes a part of $f$ (`neg`). A formula denotes a
set of events: a conjunction is verified by the fusions of verifiers of its conjuncts and a
disjunction by the verifiers of its disjuncts (`denote`). It is true at a world that contains one
of its verifiers.

An E-frame (`IsEFrame`) is a symmetric exclusion relation under which every possible event is part
of a world (`Cosmopolitan`), every event that does not conflict with some world is possible
(`Harmony`), and two possible events that do not conflict have a possible fusion
(`Truthmaker.PossibleFusion`). In the canonical frame, where a literal excludes its mirror image,
these hold (`isEFrame_excl`) and the worlds are the valuations (`worldEquiv`).

The events containing a verifier of the negation of `φ` are those that conflict with every verifier
of `φ` (`coe_upperClosure_neg`), which under Fine's Upward Exclusion are also the events containing
a verifier of his exclusive negation (`upperClosure_neg_eq`). Under Harmony and Rashōmon a world
conflicts with every event it does not contain (`conflict_of_not_le`), so it contains a verifier of
the negation of `φ` exactly when it contains no verifier of `φ` (`mem_upperClosure_neg_iff`), truth
at a world follows the classical truth tables (`mem_upperClosure_denote_iff`), and a formula is
classically valid exactly when it is true at every world of every E-frame (`forall_realize_iff`).

An emergent excluder of a set `P` excludes the fusion of `P` without lying in the regular closure
of the excluders of its members (`IsEmergentExcluder`). Fine's Downward Exclusion says there are
none (`downwardExclusion_iff`). An event that excludes `p ⊔ q` and conflicts with neither verifies
`¬(P ∧ Q)` but not `¬P ∨ ¬Q` (`mem_neg_sups_diff`), as the third egg's being in a basket with room
for two does (`eggs_mem_neg_sups_diff`). The negation of a disjunction is contained in the
conjunction of the negations (`neg_union_subset`), with equality when exclusion is cumulative
(`neg_union`).

## Implementation notes

The paper takes events to form a complete distributive lattice with a designated world. No proof
here uses distributivity, and the designated world is an argument, so occurrence is parthood in
it. `IsEFrame` is stated over complete lattices. The canonical frame is a powerset, so
`forall_realize_iff` and `exists_realize_iff` hold equally with the frames restricted to
distributive or Boolean ones (`forall_realize_iff_canonical`). Symmetry of exclusion is needed only
for Plenitude, which the paper states with the event before the world while Harmony puts the world
first, and for the comparison with worlds that are maximal with respect to compatibility. Formulas
are those of `PlebaniRosellaSaitta2022.Formula`.

## TODO

Necessity of events and propositions, loose verification, and the exact, inexact and analytic
consequence relations are not formalized.

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

open SetFamily Truthmaker PlebaniRosellaSaitta2022
open scoped Bilattice

universe u

namespace ChampollionBernard2024

variable {E A : Type*} [CompleteLattice E] {excl : E → E → Prop}

/-! ### Worlds and the axioms on exclusion -/

variable (excl) in
/-- (19): Cosmopolitanism holds when every possible event is part of a world, a maximal possible
event. -/
def Cosmopolitan : Prop :=
  ∀ e ∈ possible excl, ∃ w, e ≤ w ∧ Maximal (· ∈ possible excl) w

variable (excl) in
/-- (20): Harmony holds when every event that does not conflict with some world is possible. -/
def Harmony : Prop :=
  ∀ ⦃w e : E⦄, Maximal (· ∈ possible excl) w → ¬ Conflict excl w e → e ∈ possible excl

variable (excl) in
/-- (22): An exclusion relation is an E-frame when it is symmetric and satisfies Cosmopolitanism,
Harmony and Rashōmon. -/
@[mk_iff]
structure IsEFrame : Prop where
  /-- An event excludes the events that exclude it. -/
  symm : Std.Symm excl
  /-- Every possible event is part of a world. -/
  cosmopolitan : Cosmopolitan excl
  /-- Every event that does not conflict with some world is possible. -/
  harmony : Harmony excl
  /-- Two possible events that do not conflict have a possible fusion. -/
  possibleFusion : PossibleFusion excl

-- Theorem 8.3 (Plenitude)
theorem mem_possible_iff_exists_world [Std.Symm excl] (hC : Cosmopolitan excl)
    (hH : Harmony excl) {e : E} :
    e ∈ possible excl ↔ ∃ w, ¬ Conflict excl e w ∧ Maximal (· ∈ possible excl) w := by
  refine ⟨fun he ↦ ?_, fun ⟨w, hc, hw⟩ ↦ hH hw fun h ↦ hc h.symm⟩
  obtain ⟨w, hew, hw⟩ := hC e he
  exact ⟨w, fun hc ↦ hw.prop (hc.mono hew le_rfl), hw⟩

-- Theorem 8.4 (Manichaeism)
theorem conflict_of_not_le (hH : Harmony excl) (hR : PossibleFusion excl) {w e : E}
    (hw : Maximal (· ∈ possible excl) w) (he : ¬ e ≤ w) : Conflict excl w e := by
  by_contra hc
  exact he (le_sup_right.trans (hw.le_of_ge (hR hw.prop (hH hw hc) hc) le_sup_left))

-- fn. 20: Harmony holds of worlds that are maximal with respect to compatibility
theorem mem_possible_of_maximalCompat [Std.Symm excl] {w e : E} (hw : w ∈ possible excl)
    (h : MaximalCompat excl w) (hc : ¬ Conflict excl w e) : e ∈ possible excl :=
  (possible excl).lower (h fun h' ↦ hc h'.symm) hw

-- fn. 22: so does Manichaeism
theorem conflict_of_not_le_of_maximalCompat [Std.Symm excl] {w e : E}
    (h : MaximalCompat excl w) (he : ¬ e ≤ w) : Conflict excl w e :=
  by_contra fun hc ↦ he (h fun h' ↦ hc h'.symm)

/-! ### Negation -/

variable (excl) in
/-- (29): An event verifies the negation of `φ` when it is the fusion of the values of a function
sending each verifier of `φ` to an event that excludes some part of it. -/
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

theorem mem_upperClosure_neg {φ : Set E} {x : E} :
    x ∈ upperClosure (neg excl φ) ↔ ∀ f ∈ φ, Conflict excl x f := by
  refine ⟨fun hx f hf ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, ⟨h, hh, rfl⟩, hle⟩ := mem_upperClosure.1 hx
    obtain ⟨g, hgf, hx⟩ := hh f hf
    exact ⟨h f, (le_sSup (Set.mem_image_of_mem h hf)).trans hle, g, hgf, hx⟩
  · choose! h hhx g hg hx using h
    exact mem_upperClosure.2 ⟨sSup (h '' φ), ⟨h, fun f hf ↦ ⟨g f, hg f hf, hx f hf⟩, rfl⟩,
      sSup_le (Set.forall_mem_image.2 hhx)⟩

/-- The events containing a verifier of the negation of `φ` are those that conflict with every
verifier of `φ`. -/
theorem coe_upperClosure_neg (φ : Set E) :
    (upperClosure (neg excl φ) : Set E) = upperPolar (flip (Conflict excl)) φ :=
  Set.ext fun _ ↦ mem_upperClosure_neg

theorem upperClosure_neg_eq (hU : UpwardExclusion excl) (φ : Set E) :
    upperClosure (neg excl φ) = upperClosure (exclusiveNeg excl φ) :=
  SetLike.coe_injective ((coe_upperClosure_neg φ).trans (coe_upperClosure_exclusiveNeg hU φ).symm)

-- Theorem 9.4 (No Gluts)
theorem not_mem_upperClosure_neg {φ : Set E} {s : E} (hs : s ∈ possible excl)
    (hφ : s ∈ upperClosure φ) : s ∉ upperClosure (neg excl φ) := fun hn ↦
  let ⟨f, hf, hfs⟩ := mem_upperClosure.1 hφ
  hs ((mem_upperClosure_neg.1 hn f hf).mono le_rfl hfs)

-- Theorem 9.3 (No Gaps)
theorem mem_upperClosure_or_neg (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (φ : Set E) :
    w ∈ upperClosure φ ∨ w ∈ upperClosure (neg excl φ) :=
  or_iff_not_imp_left.2 fun hφ ↦ mem_upperClosure_neg.2 fun f hf ↦
    conflict_of_not_le hH hR hw fun hfw ↦ hφ (mem_upperClosure.2 ⟨f, hf, hfw⟩)

/-- Under Harmony and Rashōmon, a world contains a verifier of the negation of `φ` exactly when it
contains no verifier of `φ`. -/
theorem mem_upperClosure_neg_iff (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) {φ : Set E} :
    w ∈ upperClosure (neg excl φ) ↔ w ∉ upperClosure φ :=
  ⟨fun hn hφ ↦ not_mem_upperClosure_neg hw.prop hφ hn,
    (mem_upperClosure_or_neg hH hR hw φ).resolve_left⟩

theorem exclusive_mk_neg (φ : Set E) : Exclusive (possible excl) (.mk φ (neg excl φ)) :=
  exclusive_iff.2 fun _ hs hφ ↦ not_mem_upperClosure_neg hs hφ

theorem exhaustive_mk_neg (hC : Cosmopolitan excl) (hH : Harmony excl) (hR : PossibleFusion excl)
    (φ : Set E) : Exhaustive (possible excl) (.mk φ (neg excl φ)) :=
  (exhaustive_iff hC).2 fun _ hw ↦ mem_upperClosure_or_neg hH hR hw φ

theorem neg_union_subset (φ ψ : Set E) : neg excl (φ ∪ ψ) ⊆ neg excl φ ⊻ neg excl ψ := by
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨_, ⟨h, fun f hf ↦ hh f (.inl hf), rfl⟩, _, ⟨h, fun f hf ↦ hh f (.inr hf), rfl⟩,
    by rw [Set.image_union, sSup_union]⟩

theorem neg_union
    (hCum : ∀ ⦃e e' f f' : E⦄, excl e e' → excl f f' → excl (e ⊔ f) (e' ⊔ f')) (φ ψ : Set E) :
    neg excl (φ ∪ ψ) = neg excl φ ⊻ neg excl ψ := by
  classical
  refine (neg_union_subset φ ψ).antisymm ?_
  rintro _ ⟨_, ⟨h₁, hh₁, rfl⟩, _, ⟨h₂, hh₂, rfl⟩, rfl⟩
  refine ⟨fun f ↦ if f ∈ φ then if f ∈ ψ then h₁ f ⊔ h₂ f else h₁ f else h₂ f, fun f hf ↦ ?_,
    le_antisymm (sSup_le ?_) (sup_le (sSup_le ?_) (sSup_le ?_))⟩
  · by_cases h1 : f ∈ φ <;> by_cases h2 : f ∈ ψ
    · obtain ⟨g₁, hg₁, hx₁⟩ := hh₁ f h1
      obtain ⟨g₂, hg₂, hx₂⟩ := hh₂ f h2
      simpa [h1, h2] using ⟨g₁ ⊔ g₂, sup_le hg₁ hg₂, hCum hx₁ hx₂⟩
    · simpa [h1, h2] using hh₁ f h1
    · simpa [h1, h2] using hh₂ f h2
    · exact absurd hf (by simp [h1, h2])
  · rintro _ ⟨f, hf, rfl⟩
    by_cases h1 : f ∈ φ <;> by_cases h2 : f ∈ ψ <;> simp only [h1, h2, ↓reduceIte]
    · exact sup_le_sup (le_sSup ⟨f, h1, rfl⟩) (le_sSup ⟨f, h2, rfl⟩)
    · exact le_sup_of_le_left (le_sSup ⟨f, h1, rfl⟩)
    · exact le_sup_of_le_right (le_sSup ⟨f, h2, rfl⟩)
    · exact absurd hf (by simp [h1, h2])
  · rintro _ ⟨f, hf, rfl⟩
    refine le_trans ?_ (le_sSup ⟨f, .inl hf, rfl⟩)
    by_cases h2 : f ∈ ψ <;> simp [hf, h2]
  · rintro _ ⟨f, hf, rfl⟩
    refine le_trans ?_ (le_sSup ⟨f, .inr hf, rfl⟩)
    by_cases h1 : f ∈ φ <;> simp [hf, h1]

/-! ### Formulas -/

variable (excl) in
/-- (26), (27), (29): The proposition a formula expresses when `I` assigns verifiers to the
atoms. -/
def denote (I : A → Set E) : Formula A → Set E
  | .atom a => I a
  | .neg φ => neg excl (denote I φ)
  | .conj φ ψ => denote I φ ⊻ denote I ψ
  | .disj φ ψ => denote I φ ∪ denote I ψ

/-- A formula is realized by a valuation when the classical truth tables make it true. -/
def Realize (v : A → Prop) : Formula A → Prop
  | .atom a => v a
  | .neg φ => ¬ Realize v φ
  | .conj φ ψ => Realize v φ ∧ Realize v ψ
  | .disj φ ψ => Realize v φ ∨ Realize v ψ

/-- Under Harmony and Rashōmon, a formula is true at a world exactly when it is realized by the
valuation making an atom true when the world contains one of its verifiers. -/
theorem mem_upperClosure_denote_iff (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (I : A → Set E) (φ : Formula A) :
    w ∈ upperClosure (denote excl I φ) ↔ Realize (fun a ↦ w ∈ upperClosure (I a)) φ := by
  induction φ with
  | atom a => rfl
  | neg φ ih => exact (mem_upperClosure_neg_iff hH hR hw).trans ih.not
  | conj φ ψ ihφ ihψ =>
    simp only [denote, Realize, upperClosure_sups, UpperSet.mem_sup_iff, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [denote, Realize, upperClosure_union, UpperSet.mem_inf_iff, ihφ, ihψ]

/-! ### Emergent exclusion and de Morgan's law -/

variable (excl) in
/-- (13): An emergent excluder of `P` excludes the fusion of `P` without lying in the regular
closure of the excluders of members of `P`. -/
def IsEmergentExcluder (s : E) (P : Set E) : Prop :=
  excl s (sSup P) ∧ s ∉ regularClosure {r | ∃ p ∈ P, excl r p}

theorem downwardExclusion_iff :
    DownwardExclusion excl ↔ ∀ s P, ¬ IsEmergentExcluder excl s P :=
  ⟨fun h _ _ hs ↦ hs.2 (h hs.1), fun h _ _ hs ↦ by_contra fun hn ↦ h _ _ ⟨hs, hn⟩⟩

theorem not_mem_regularClosure_excluders {P : Set E} {s : E}
    (hc : ∀ p ∈ P, ¬ Conflict excl s p) : s ∉ regularClosure {r | ∃ p ∈ P, excl r p} :=
  fun ⟨hs, _⟩ ↦
    let ⟨r, ⟨p, hp, hx⟩, hrs⟩ := mem_upperClosure.1 hs
    hc p hp ⟨r, hrs, p, le_rfl, hx⟩

theorem IsEmergentExcluder.of_forall_not_conflict {P : Set E} {s : E} (hs : excl s (sSup P))
    (hc : ∀ p ∈ P, ¬ Conflict excl s p) : IsEmergentExcluder excl s P :=
  ⟨hs, not_mem_regularClosure_excluders hc⟩

/-- An event excluding `p ⊔ q` that conflicts with neither `p` nor `q` verifies `¬(P ∧ Q)` but not
`¬P ∨ ¬Q`. -/
theorem mem_neg_sups_diff {p q s : E} (hs : excl s (p ⊔ q)) (hp : ¬ Conflict excl s p)
    (hq : ¬ Conflict excl s q) : s ∈ neg excl ({p} ⊻ {q}) \ (neg excl {p} ∪ neg excl {q}) := by
  rw [Set.singleton_sups_singleton, neg_singleton, neg_singleton, neg_singleton]
  refine ⟨⟨p ⊔ q, le_rfl, hs⟩, ?_⟩
  rintro (⟨g, hg, hx⟩ | ⟨g, hg, hx⟩)
  · exact hp ⟨s, le_rfl, g, hg, hx⟩
  · exact hq ⟨s, le_rfl, g, hg, hx⟩

-- §9: the two sides of de Morgan's law `¬(φ ∧ ψ) ⇔ ¬φ ∨ ¬ψ` hold at the same worlds
theorem mem_upperClosure_neg_sups_iff (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (φ ψ : Set E) :
    w ∈ upperClosure (neg excl (φ ⊻ ψ)) ↔ w ∈ upperClosure (neg excl φ ∪ neg excl ψ) := by
  rw [upperClosure_union, UpperSet.mem_inf_iff, mem_upperClosure_neg_iff hH hR hw,
    mem_upperClosure_neg_iff hH hR hw, mem_upperClosure_neg_iff hH hR hw, upperClosure_sups,
    UpperSet.mem_sup_iff, not_and_or]

-- §8, fn. 27: if exclusion is cumulative, fusing verifiers of `¬P` and `¬Q` verifies `¬(P ∧ Q)`
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

-- fn. 21: under Upward Exclusion, Rashōmon is Fine's second condition on classical exclusion
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
the basket excludes the event of the other two eggs' being in it, and conversely. -/
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

private theorem eggsExcl_two : eggsExcl {2} ({0} ⊔ {1}) :=
  ⟨2, .inl ⟨rfl, by ext x; fin_cases x <;> simp⟩⟩

-- §7: the third egg's being in the basket verifies *egg 1 and egg 2 are not both in the basket*
-- but not the disjunction of the negations
theorem eggs_mem_neg_sups_diff :
    ({2} : Set (Fin 3)) ∈
      neg eggsExcl ({{0}} ⊻ {{1}}) \ (neg eggsExcl {{0}} ∪ neg eggsExcl {{1}}) :=
  mem_neg_sups_diff eggsExcl_two (not_conflict_eggsExcl 2 0) (not_conflict_eggsExcl 2 1)

theorem isEmergentExcluder_eggs : IsEmergentExcluder eggsExcl {2} {{0}, {1}} :=
  .of_forall_not_conflict (by rw [sSup_pair]; exact eggsExcl_two) <| by
    rintro _ (rfl | rfl)
    exacts [not_conflict_eggsExcl 2 0, not_conflict_eggsExcl 2 1]

/-! ### The canonical frame -/

section Canonical

open Truthmaker.Canonical

variable {α : Type*}

theorem neg_pro_atom (a : α) : neg Canonical.excl (atom a).pro = (atom a).con := by
  rw [pro_atom, con_atom, neg_singleton]
  ext e
  constructor
  · rintro ⟨_, hg, x, rfl, rfl⟩
    obtain rfl : x = (a, false) := by
      simpa using congrArg mirror (Set.singleton_subset_singleton.1 hg)
    rfl
  · rintro rfl
    exact ⟨{(a, true)}, le_rfl, (a, false), rfl, rfl⟩

-- §9: in the canonical frame the negation of a conjunction of two atoms is verified exactly by
-- its falsifiers
theorem neg_pro_conj_atom (a b : α) :
    neg Canonical.excl (conj (atom a) (atom b)).pro = (conj (atom a) (atom b)).con := by
  rw [pro_conj, con_conj, pro_atom, pro_atom, con_atom, con_atom,
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

theorem harmony_excl : Harmony (Canonical.excl (α := α)) := by
  intro w e hw hc
  rw [possible_excl] at hw ⊢
  intro x hx hx'
  rcases mem_or_mirror_mem_of_maximal hw x with hxw | hxw
  · exact hc (conflict_excl_iff.2 ⟨x, hxw, hx'⟩)
  · exact hc (conflict_excl_iff.2 ⟨mirror x, hxw, by rwa [mirror_mirror]⟩)

theorem cosmopolitan_excl : Cosmopolitan (Canonical.excl (α := α)) := by
  unfold Cosmopolitan
  rw [possible_excl]
  exact fun _ ↦ exists_le_maximal_possible

theorem mk_neg_pro_atom (a : α) :
    Bilattice.Product.mk (atom a).pro (neg Canonical.excl (atom a).pro) = atom a := by
  rw [neg_pro_atom, Bilattice.Product.mk_pro_con]

/- Fine's classicality of the canonical atoms follows from the exclusion axioms. -/
example (a : α) : Exclusive Canonical.possible (atom a) :=
  possible_excl ▸ mk_neg_pro_atom a ▸ exclusive_mk_neg _

example (a : α) : Exhaustive Canonical.possible (atom a) :=
  possible_excl ▸ mk_neg_pro_atom a ▸
    exhaustive_mk_neg cosmopolitan_excl harmony_excl
      possibleFusion_excl _

theorem isEFrame_excl : IsEFrame (Canonical.excl (α := α)) :=
  ⟨inferInstance, cosmopolitan_excl, harmony_excl, possibleFusion_excl⟩

/-- The worlds of the canonical frame are the valuations: a valuation `v` corresponds to the world
containing the literal `(a, true)` when `v a` holds and `(a, false)` otherwise. -/
def worldEquiv : (α → Prop) ≃ {w : Set (α × Bool) // Maximal (· ∈ Canonical.possible) w} where
  toFun v := ⟨{x | x.2 = true ↔ v x.1}, maximal_possible_iff.2 fun ⟨a, b⟩ ↦ by cases b <;> simp⟩
  invFun w a := (a, true) ∈ w.1
  left_inv v := by ext a; simp
  right_inv w := Subtype.ext <| Set.ext fun ⟨a, b⟩ ↦ by
    cases b
    · simpa using (maximal_possible_iff.1 w.2 (a, false)).symm
    · simp

theorem mem_worldEquiv {v : α → Prop} {a : α} {b : Bool} :
    (a, b) ∈ (worldEquiv v).1 ↔ (b = true ↔ v a) :=
  Iff.rfl

theorem worldEquiv_symm_apply (w : {w : Set (α × Bool) // Maximal (· ∈ Canonical.possible) w})
    (a : α) : worldEquiv.symm w a ↔ (a, true) ∈ w.1 :=
  Iff.rfl

theorem mem_upperClosure_denote_worldEquiv (v : α → Prop) (φ : Formula α) :
    (worldEquiv v).1 ∈ upperClosure (denote Canonical.excl (fun a ↦ (atom a).pro) φ) ↔
      Realize v φ := by
  rw [mem_upperClosure_denote_iff harmony_excl possibleFusion_excl
    (by rw [possible_excl]; exact (worldEquiv v).2)]
  exact iff_of_eq (congrArg (Realize · φ) (funext fun a ↦ propext (by simp [mem_worldEquiv])))

theorem forall_realize_iff_canonical (φ : Formula α) :
    (∀ v, Realize v φ) ↔ ∀ w, Maximal (· ∈ Canonical.possible) w →
      w ∈ upperClosure (denote Canonical.excl (fun a ↦ (atom a).pro) φ) := by
  refine ⟨fun h w hw ↦ ?_,
    fun h v ↦ (mem_upperClosure_denote_worldEquiv v φ).1 (h _ (worldEquiv v).2)⟩
  obtain ⟨v, hv⟩ := worldEquiv.surjective ⟨w, hw⟩
  obtain rfl : (worldEquiv v).1 = w := congrArg Subtype.val hv
  exact (mem_upperClosure_denote_worldEquiv v φ).2 (h v)

end Canonical

/-! ### Classical validity and satisfiability -/

/-- A formula is realized by every valuation exactly when it is true at every world of every
E-frame under every interpretation. -/
theorem forall_realize_iff {A : Type u} (φ : Formula A) :
    (∀ v, Realize v φ) ↔ ∀ (E : Type u) [CompleteLattice E] (excl : E → E → Prop)
      (I : A → Set E) (w : E), IsEFrame excl → Maximal (· ∈ possible excl) w →
        w ∈ upperClosure (denote excl I φ) :=
  ⟨fun h _ _ _ I _ hE hw ↦
      (mem_upperClosure_denote_iff hE.harmony hE.possibleFusion hw I φ).2 (h _),
    fun h ↦ (forall_realize_iff_canonical φ).2 fun w hw ↦
      h _ _ _ w isEFrame_excl (by rwa [Canonical.possible_excl])⟩

-- Theorem 9.8
theorem exists_realize_iff {A : Type u} (φ : Formula A) :
    (∃ v, Realize v φ) ↔ ∃ (E : Type u) (_ : CompleteLattice E) (excl : E → E → Prop)
      (I : A → Set E) (w : E), IsEFrame excl ∧ Maximal (· ∈ possible excl) w ∧
        w ∈ upperClosure (denote excl I φ) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨_, inferInstance, _, _, _, isEFrame_excl,
      by rw [Canonical.possible_excl]; exact (worldEquiv v).2,
      (mem_upperClosure_denote_worldEquiv v φ).2 hv⟩,
    fun ⟨_, _, _, I, _, hE, hw, h⟩ ↦
      ⟨_, (mem_upperClosure_denote_iff hE.harmony hE.possibleFusion hw I φ).1 h⟩⟩

end ChampollionBernard2024
