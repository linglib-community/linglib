module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Exhaustification.Alternatives
public import Studies.Spector2007

/-!
# Fagen (2026): Order selection: the logical foundations of exhaustivity

Fagen derives the exhaustive interpretation of an answer from its meaning and the question, with
no theory of alternative sentences: following Schulz and van Rooij, an answer holds in the best
worlds where it is true, and what varies is the order that ranks the worlds. The default order
minimizes the question-property, which gives a positive answer such as *Agnes* its negative
direction and unrestricted extent; under it exhaustive interpretation is [the minimal-worlds
exhaustifier over the question's propositions](##Fagen2026.exh_ltDefault). A negative or mixed
answer is only about its restriction, the intersection of the sets it lives on, which [the
positive and negative restrictions make
up](##Fagen2026.positiveRestriction_union_negativeRestriction); the hybrid order minimizes the
question-property within the first and maximizes it within the second, so that [nothing outside
the restriction is concluded](##Fagen2026.mem_exh_ltHybrid_iff_of_inter).
Positive skew, a restriction equal to the positive restriction, selects the default order. *Some
of the linguists but not all of the computer scientists* is not positively skewed, and the hybrid
order [makes exactly one linguist and all but one computer scientist
attend](##Fagen2026.exh_selectedOrder_someButNotAll). Positive skew is exactly [Spector's
quasi-positivity](##Fagen2026.quasiPositive_iff_positivelySkewed), which Spector stated over
formulae of a propositional language.

## Implementation notes

* An answer is a quantifier `T` over individuals and the question a property `P : W → Set E` of
  worlds; exhaustive interpretation `exh P T r` takes the order `r` as a parameter, as (29) does.
* The worked examples take the worlds to be all extensions of the question-property, as Fagen's
  diagrams do.
* A proposition of Spector's question-relative language, a set of valuations of the atoms, is a
  quantifier over the atoms, `quantifierOf`.

## Errata

* The hybrid order (31) is not transitive once an answer's positive and negative restrictions
  each have three members, as in *some of the linguists but not all of the computer scientists*
  with three of each (`not_transitive_ltHybrid`); Fagen calls it an order and notes only that it is
  antisymmetric. Exhaustive interpretation is defined from the relation itself, so his predictions
  stand.
* The proof that a quantifier lives on its restriction (A4) ends by claiming the result for any
  countable family of live-on sets; it holds only for finitely many, and fails for the cofinite
  sets of numbers (`not_livesOn_restriction_cofinite`). The appendix assumes a finite model, where
  the result holds (`livesOn_restriction`).

## TODO

* Preserve Restriction (26), from which §3.2 derives order selection (12), is not formalized; nor
  are answers to second-order questions (§2.4) or the conditions under which the dual order is
  chosen (§3.3).
* The answers of Table 3.1 are not recorded as data.

## References

* [L. Fagen, *Order selection: the logical foundations of exhaustivity* (2026)][fagen-2026]
* [B. Spector, *Scalar implicatures: exhaustivity and Gricean reasoning* (2007)][spector-2007]
* [J. Groenendijk and M. Stokhof, *Studies on the semantics of questions and the pragmatics of
  answers* (1984)][groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Fagen2026

open Set

variable {E : Type*}

/-! ### Restriction operators (§2.2, Appendix) -/

section Restriction

variable (T : Quantifier E)

/-- The restriction of a quantifier is the intersection of the sets it lives on ((10)). -/
def restriction : Set E := ⋂₀ {S | T.LivesOn S}

/-- The positive restriction of a quantifier holds the objects whose addition turns a set the
quantifier does not apply to into one it applies to ((18a)). -/
def positiveRestriction : Set E := {x | ∃ S, ¬ T S ∧ T (insert x S)}

/-- The negative restriction of a quantifier holds the objects whose removal turns a set the
quantifier does not apply to into one it applies to ((18b)). -/
def negativeRestriction : Set E := {x | ∃ S, ¬ T S ∧ T (S \ {x})}

variable {T} {x : E}

theorem notMem_restriction_iff : x ∉ restriction T ↔ T.LivesOn {x}ᶜ := by
  simp only [restriction, mem_sInter, mem_ofPred_eq, not_forall, exists_prop]
  exact ⟨fun ⟨S, hS, hx⟩ ↦ hS.mono (subset_compl_singleton_iff.2 hx),
    fun h ↦ ⟨_, h, fun h' ↦ h' (mem_singleton x)⟩⟩

theorem mem_restriction_iff : x ∈ restriction T ↔ ∃ S, ¬ (T S ↔ T (S \ {x})) := by
  rw [← not_iff_not, notMem_restriction_iff, not_exists]
  simp only [not_not, Quantifier.LivesOn, ← sdiff_eq_compl_inter]

-- (20a), A5
theorem mem_positiveRestriction_iff :
    x ∈ positiveRestriction T ↔ ∃ S, T S ∧ ¬ T (S \ {x}) := by
  constructor
  · rintro ⟨S, hS, hxS⟩
    have hx : x ∉ S := fun h ↦ hS (by rwa [insert_eq_of_mem h] at hxS)
    refine ⟨insert x S, hxS, ?_⟩
    rwa [insert_sdiff_of_mem _ (mem_singleton x), sdiff_singleton_eq_self hx]
  · rintro ⟨S, hS, hSx⟩
    have hx : x ∈ S := by_contra fun h ↦ hSx (by rwa [sdiff_singleton_eq_self h])
    refine ⟨S \ {x}, hSx, ?_⟩
    rwa [insert_sdiff_singleton, insert_eq_of_mem hx]

-- (20b), A6
theorem mem_negativeRestriction_iff :
    x ∈ negativeRestriction T ↔ ∃ S, T S ∧ ¬ T (insert x S) := by
  constructor
  · rintro ⟨S, hS, hSx⟩
    have hx : x ∈ S := by_contra fun h ↦ hS (by rwa [sdiff_singleton_eq_self h] at hSx)
    refine ⟨S \ {x}, hSx, ?_⟩
    rwa [insert_sdiff_singleton, insert_eq_of_mem hx]
  · rintro ⟨S, hS, hxS⟩
    have hx : x ∉ S := fun h ↦ hxS (by rwa [insert_eq_of_mem h])
    refine ⟨insert x S, hxS, ?_⟩
    rwa [insert_sdiff_of_mem _ (mem_singleton x), sdiff_singleton_eq_self hx]

variable (T) in
/-- The positive and negative restrictions of a quantifier make up its restriction (A7). -/
theorem positiveRestriction_union_negativeRestriction :
    positiveRestriction T ∪ negativeRestriction T = restriction T := by
  ext x
  rw [mem_union, mem_positiveRestriction_iff, mem_restriction_iff, negativeRestriction,
    mem_ofPred_eq, ← exists_or]
  exact exists_congr fun S ↦ by tauto

theorem positiveRestriction_subset_restriction : positiveRestriction T ⊆ restriction T :=
  positiveRestriction_union_negativeRestriction T ▸ subset_union_left

theorem negativeRestriction_subset_restriction : negativeRestriction T ⊆ restriction T :=
  positiveRestriction_union_negativeRestriction T ▸ subset_union_right

-- A4
theorem livesOn_restriction [Finite E] : T.LivesOn (restriction T) := by
  classical
  have key : ∀ F : Finset E, (∀ x ∈ F, T.LivesOn {x}ᶜ) → T.LivesOn (↑F)ᶜ := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; simpa using T.livesOn_univ
    | insert a F _ ih =>
      intro h
      rw [Finset.coe_insert, insert_eq, compl_union]
      exact (h a (Finset.mem_insert_self a F)).inter
        (ih fun x hx ↦ h x (Finset.mem_insert_of_mem hx))
  simpa using key (restriction T)ᶜ.toFinite.toFinset
    fun x hx ↦ notMem_restriction_iff.1 (by simpa using hx)

-- A4 on an infinite domain
theorem not_livesOn_restriction_cofinite :
    ¬ Quantifier.LivesOn (fun S : Set ℕ ↦ Sᶜ.Finite) (restriction fun S : Set ℕ ↦ Sᶜ.Finite) := by
  have hR : restriction (fun S : Set ℕ ↦ Sᶜ.Finite) = ∅ := by
    refine eq_empty_of_forall_notMem fun x ↦ notMem_restriction_iff.2 fun B ↦ ?_
    rw [compl_inter, compl_compl]
    exact ⟨fun h ↦ (finite_singleton x).union h, fun h ↦ h.subset subset_union_right⟩
  rw [hR]
  intro h
  exact infinite_univ (by simpa using (h univ).1 (by simp))

theorem negativeRestriction_eq_empty_of_monotone (hT : Monotone T) :
    negativeRestriction T = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, hS, h⟩ ↦ hS (hT sdiff_subset h)

theorem positiveRestriction_eq_empty_of_antitone (hT : Antitone T) :
    positiveRestriction T = ∅ :=
  eq_empty_of_forall_notMem fun x ⟨S, hS, h⟩ ↦ hS (hT (subset_insert x S) h)

-- A9
theorem negativeRestriction_eq_empty_iff [Finite E] :
    negativeRestriction T = ∅ ↔ Monotone T := by
  classical
  refine ⟨fun h A B hAB hA ↦ ?_, negativeRestriction_eq_empty_of_monotone⟩
  have step : ∀ x S, T S → T (insert x S) := fun x S hS ↦ not_not.1 fun hn ↦
    (eq_empty_iff_forall_notMem.1 h x) (mem_negativeRestriction_iff.2 ⟨S, hS, hn⟩)
  have key : ∀ F : Finset E, T (A ∪ ↑F) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hA
    | insert a F _ ih => rw [Finset.coe_insert, union_insert]; exact step a _ ih
  have := key (B \ A).toFinite.toFinset
  rwa [Finite.coe_toFinset, union_sdiff_cancel hAB] at this

-- A10
theorem positiveRestriction_eq_empty_iff [Finite E] :
    positiveRestriction T = ∅ ↔ Antitone T := by
  classical
  refine ⟨fun h A B hAB hB ↦ ?_, positiveRestriction_eq_empty_of_antitone⟩
  have step : ∀ x S, T S → T (S \ {x}) := fun x S hS ↦ not_not.1 fun hn ↦
    (eq_empty_iff_forall_notMem.1 h x) (mem_positiveRestriction_iff.2 ⟨S, hS, hn⟩)
  have key : ∀ F : Finset E, T (B \ ↑F) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hB
    | insert a F _ ih =>
      rw [Finset.coe_insert, insert_eq, union_comm, ← sdiff_sdiff]; exact step a _ ih
  have := key (B \ A).toFinite.toFinset
  rwa [Finite.coe_toFinset, sdiff_sdiff_cancel_left hAB] at this

variable (T) in
/-- A quantifier is positively skewed when its restriction is its positive restriction ((2)). -/
def PositivelySkewed : Prop := restriction T = positiveRestriction T

variable (T) in
/-- A quantifier is negatively skewed when its restriction is its negative restriction ((2)). -/
def NegativelySkewed : Prop := restriction T = negativeRestriction T

theorem positivelySkewed_iff : PositivelySkewed T ↔ negativeRestriction T ⊆ positiveRestriction T :=
  by rw [PositivelySkewed, ← positiveRestriction_union_negativeRestriction, union_eq_left]

theorem negativelySkewed_iff : NegativelySkewed T ↔ positiveRestriction T ⊆ negativeRestriction T :=
  by rw [NegativelySkewed, ← positiveRestriction_union_negativeRestriction, union_eq_right]

-- A12
theorem positivelySkewed_of_monotone (hT : Monotone T) : PositivelySkewed T :=
  positivelySkewed_iff.2 (negativeRestriction_eq_empty_of_monotone hT ▸ empty_subset _)

-- A13
theorem negativelySkewed_of_antitone (hT : Antitone T) : NegativelySkewed T :=
  negativelySkewed_iff.2 (positiveRestriction_eq_empty_of_antitone hT ▸ empty_subset _)

end Restriction

/-! ### Orders over worlds (§2.1, §2.3, §3.3) -/

section Orders

variable {W : Type*} (P : W → Set E) (T : Quantifier E)

/-- The default order ranks worlds by inclusion of the question-property ((30)). -/
def ltDefault (v w : W) : Prop := P v ⊂ P w

/-- The positive component of the hybrid order ((31a)). -/
def ltPos (v w : W) : Prop :=
  P v ∩ positiveRestriction T ⊂ P w ∩ positiveRestriction T

/-- The negative component of the hybrid order ((31b)). -/
def ltNeg (v w : W) : Prop :=
  P w ∩ negativeRestriction T ⊂ P v ∩ negativeRestriction T

/-- `v` is hybrid-below `w` when it is below by either component ((31c)). -/
def leHybrid (v w : W) : Prop := ltPos P T v w ∨ ltNeg P T v w

/-- The hybrid order keeps the pairs on which the two components do not conflict ((31d)). -/
def ltHybrid (v w : W) : Prop := leHybrid P T v w ∧ ¬ leHybrid P T w v

/-- The dual order ranks worlds by reverse inclusion of the question-property ((39)). -/
def ltDual (v w : W) : Prop := P w ⊂ P v

/-- Exhaustive interpretation keeps the worlds where the answer holds of the question-property
and no such world lies below by the order `r` ((29)). -/
def exh (r : W → W → Prop) : Set W := {w | T (P w) ∧ ¬ ∃ v, T (P v) ∧ r v w}

open Classical in
/-- Order selection: a positively skewed answer takes the default order and any other answer the
hybrid order ((12)). -/
noncomputable def selectedOrder : W → W → Prop :=
  if PositivelySkewed T then ltDefault P else ltHybrid P T

open Exhaustification in
/-- Under the default order, exhaustive interpretation is the minimal-worlds exhaustifier over the
propositions that the question-property holds of each individual ((83)). -/
theorem exh_ltDefault :
    exh P T (ltDefault P) = exhMW (range fun x ↦ {w | x ∈ P w}) {w | T (P w)} := by
  have h : ∀ v w, (v <[range fun x ↦ {w | x ∈ P w}] w) ↔ ltDefault P v w := fun v w ↦ by
    simp only [ltALT_iff, leALT_iff, forall_mem_range, ltDefault, ssubset_def, subset_def]
    rfl
  ext w
  simp only [exh, mem_exhMW, mem_ofPred_eq, h]

-- p. 70: the hybrid order is antisymmetric
theorem ltHybrid_asymm {v w : W} (h : ltHybrid P T v w) : ¬ ltHybrid P T w v :=
  fun h' ↦ h.2 h'.1

variable {P T}

theorem ltHybrid_iff_of_inter_eq {v v' w w' : W} (hv : P v ∩ restriction T = P v' ∩ restriction T)
    (hw : P w ∩ restriction T = P w' ∩ restriction T) :
    ltHybrid P T v w ↔ ltHybrid P T v' w' := by
  have hp : ∀ u, P u ∩ positiveRestriction T = (P u ∩ restriction T) ∩ positiveRestriction T :=
    fun u ↦ by rw [inter_assoc, inter_eq_right.2 positiveRestriction_subset_restriction]
  have hn : ∀ u, P u ∩ negativeRestriction T = (P u ∩ restriction T) ∩ negativeRestriction T :=
    fun u ↦ by rw [inter_assoc, inter_eq_right.2 negativeRestriction_subset_restriction]
  simp only [ltHybrid, leHybrid, ltPos, ltNeg, hp v, hp w, hn v, hn w, hv, hw, ← hp, ← hn]

/-- Exhaustive interpretation with the hybrid order treats alike two worlds that agree within the
answer's restriction, so it concludes nothing about objects outside it (§2.2.1). -/
theorem mem_exh_ltHybrid_iff_of_inter [Finite E] {w w' : W}
    (h : P w ∩ restriction T = P w' ∩ restriction T) :
    w ∈ exh P T (ltHybrid P T) ↔ w' ∈ exh P T (ltHybrid P T) := by
  have hT : T (P w) ↔ T (P w') := by
    rw [livesOn_restriction (T := T) (P w), livesOn_restriction (T := T) (P w'), inter_comm, h,
      inter_comm]
  simp only [exh, mem_ofPred_eq, hT, ltHybrid_iff_of_inter_eq rfl h]

end Orders

/-! ### Worked examples (§2.1.2, §2.3) -/

section Examples

open Quantifier

-- (6): *Agnes* takes the default order and says that Agnes alone has the property
theorem exh_selectedOrder_individual (a : E) :
    exh id (individual a) (selectedOrder id (individual a)) = {{a}} := by
  have hmono : Monotone (individual a) := fun _ _ h ha ↦ h ha
  simp only [selectedOrder, positivelySkewed_of_monotone hmono, ↓reduceIte]
  ext S
  simp only [exh, mem_ofPred_eq, individual, ltDefault, id, mem_singleton_iff, not_exists, not_and]
  constructor
  · rintro ⟨ha, h⟩
    by_contra hne
    exact h {a} (mem_singleton a)
      (ssubset_iff_subset_ne.2 ⟨singleton_subset_iff.2 ha, fun h' ↦ hne h'.symm⟩)
  · rintro rfl
    exact ⟨mem_singleton a, fun v hv hlt ↦ hlt.ne (hlt.subset.antisymm (singleton_subset_iff.2 hv))⟩

-- (33): *not Beatrice* licenses nothing beyond itself
theorem exh_ltHybrid_not (b : E) :
    exh id (fun S ↦ b ∉ S) (ltHybrid id fun S ↦ b ∉ S) = {S | b ∉ S} := by
  ext S
  refine ⟨fun h ↦ h.1, fun hS ↦ ⟨hS, ?_⟩⟩
  rintro ⟨v, hv, (hpos | hneg), -⟩
  · obtain ⟨y, ⟨-, hy⟩, -⟩ := exists_of_ssubset hpos
    rw [positiveRestriction_eq_empty_of_antitone (T := fun S ↦ b ∉ S)
      fun _ _ h hB hA ↦ hB (h hA)] at hy
    exact hy
  · obtain ⟨y, ⟨hyv, S', hS', hS'y⟩, -⟩ := exists_of_ssubset hneg
    have hyb : y = b := by_contra fun hne ↦ hS'y ⟨not_not.1 hS', fun h ↦ hne h.symm⟩
    exact hv (hyb ▸ hyv)

-- (39), §3.3.1: under the dual order *not Beatrice* says that everyone else has the property
theorem exh_ltDual_not (b : E) : exh id (fun S ↦ b ∉ S) (ltDual id) = {{b}ᶜ} := by
  ext S
  simp only [exh, mem_ofPred_eq, ltDual, id, mem_singleton_iff, not_exists, not_and]
  constructor
  · rintro ⟨hb, h⟩
    by_contra hne
    exact h {b}ᶜ (fun h' ↦ h' rfl)
      (ssubset_iff_subset_ne.2 ⟨subset_compl_singleton_iff.2 hb, hne⟩)
  · rintro rfl
    exact ⟨fun h ↦ h rfl,
      fun v hv hlt ↦ not_subset_of_ssubset hlt (subset_compl_singleton_iff.2 hv)⟩

variable {L C : Set E}

/-- *Some of the `L` but not all of the `C`*. -/
def someButNotAll (L C : Set E) : Quantifier E := fun S ↦ (S ∩ L).Nonempty ∧ ¬ C ⊆ S

theorem positiveRestriction_someButNotAll (hLC : Disjoint L C) (hC : C.Nonempty) :
    positiveRestriction (someButNotAll L C) = L := by
  ext x
  constructor
  · rintro ⟨S, hS, ⟨y, hyS, hyL⟩, hCS⟩
    by_contra hx
    refine hS ⟨⟨y, ?_, hyL⟩, fun h ↦ hCS (h.trans (subset_insert x S))⟩
    rcases hyS with rfl | hyS
    · exact absurd hyL hx
    · exact hyS
  · intro hx
    refine ⟨∅, fun h ↦ (h.1.ne_empty (by simp)), ⟨x, by simp, hx⟩, fun h ↦ ?_⟩
    obtain ⟨c, hc⟩ := hC
    have hcx : c = x := by simpa using h hc
    exact hLC.ne_of_mem hx (hcx ▸ hc) rfl

theorem negativeRestriction_someButNotAll (hLC : Disjoint L C) (hL : L.Nonempty) :
    negativeRestriction (someButNotAll L C) = C := by
  ext x
  constructor
  · rintro ⟨S, hS, ⟨y, hyS, hyL⟩, hCS⟩
    by_contra hx
    exact hS ⟨⟨y, hyS.1, hyL⟩, fun h ↦ hCS fun c hc ↦ ⟨h hc, fun hcx ↦ hx (hcx ▸ hc)⟩⟩
  · intro hx
    obtain ⟨l, hl⟩ := hL
    refine ⟨L ∪ C, fun h ↦ h.2 subset_union_right, ⟨l, ⟨.inl hl, ?_⟩, hl⟩, fun h ↦ ?_⟩
    · rintro rfl
      exact hLC.ne_of_mem hl hx rfl
    · exact (h hx).2 rfl

theorem not_positivelySkewed_someButNotAll (hLC : Disjoint L C) (hL : L.Nonempty)
    (hC : C.Nonempty) : ¬ PositivelySkewed (someButNotAll L C) := fun h ↦ by
  rw [positivelySkewed_iff, positiveRestriction_someButNotAll hLC hC,
    negativeRestriction_someButNotAll hLC hL] at h
  obtain ⟨c, hc⟩ := hC
  exact hLC.ne_of_mem (h hc) hc rfl

/-- *Some of the `L` but not all of the `C`* takes the hybrid order and says that exactly one `L`
and all but one `C` have the property ((40)). -/
theorem exh_selectedOrder_someButNotAll (hLC : Disjoint L C) (hL : L.Nonempty)
    (hC : C.Nonempty) :
    exh id (someButNotAll L C) (selectedOrder id (someButNotAll L C)) =
      {S | (∃ l, S ∩ L = {l}) ∧ ∃ c, C \ S = {c}} := by
  simp only [selectedOrder, not_positivelySkewed_someButNotAll hLC hL hC, ↓reduceIte]
  have hd : ∀ z, z ∈ L → z ∉ C := fun z hz hz' ↦ hLC.ne_of_mem hz hz' rfl
  have hlt : ∀ v w : Set E, ltHybrid id (someButNotAll L C) v w ↔
      (v ∩ L ⊂ w ∩ L ∨ w ∩ C ⊂ v ∩ C) ∧ ¬ (w ∩ L ⊂ v ∩ L ∨ v ∩ C ⊂ w ∩ C) := fun v w ↦ by
    simp only [ltHybrid, leHybrid, ltPos, ltNeg, positiveRestriction_someButNotAll hLC hC,
      negativeRestriction_someButNotAll hLC hL, id]
  ext S
  simp only [exh, mem_ofPred_eq, id, hlt, someButNotAll]
  constructor
  · rintro ⟨⟨⟨y, hyS, hyL⟩, hCS⟩, hmin⟩
    obtain ⟨c, hcC, hcS⟩ := not_subset.1 hCS
    refine ⟨⟨y, eq_singleton_iff_unique_mem.2 ⟨⟨hyS, hyL⟩, fun l ⟨hlS, hlL⟩ ↦ ?_⟩⟩,
      ⟨c, eq_singleton_iff_unique_mem.2 ⟨⟨hcC, hcS⟩, fun d ⟨hdC, hdS⟩ ↦ ?_⟩⟩⟩
    · -- a second linguist: drop every linguist but `y`
      by_contra hly
      have hvL : ∀ z, z ∈ (S \ L) ∪ {y} → z ∈ L → z = y := fun z hz hzL ↦
        hz.elim (fun h ↦ absurd hzL h.2) id
      have hvC : ∀ z ∈ C, z ∈ (S \ L) ∪ {y} ↔ z ∈ S := fun z hzC ↦
        ⟨fun h ↦ h.elim And.left fun h ↦ absurd (h ▸ hyL) (fun h' ↦ hd z h' hzC),
          fun h ↦ .inl ⟨h, fun h' ↦ hd z h' hzC⟩⟩
      refine hmin ⟨(S \ L) ∪ {y}, ⟨⟨y, .inr rfl, hyL⟩, fun h ↦ hcS ((hvC c hcC).1 (h hcC))⟩,
        .inl (ssubset_iff_of_subset (fun z (hz : z ∈ ((S \ L) ∪ {y}) ∩ L) ↦
          hvL z hz.1 hz.2 ▸ ⟨hyS, hyL⟩) |>.2
          ⟨l, ⟨hlS, hlL⟩, fun ⟨hl, _⟩ ↦ hly (hvL l hl hlL)⟩), ?_⟩
      rintro (h | h)
      · exact hly (hvL l (h.subset ⟨hlS, hlL⟩).1 hlL)
      · obtain ⟨z, ⟨hzS, hzC⟩, hz⟩ := exists_of_ssubset h
        exact hz ⟨(hvC z hzC).2 hzS, hzC⟩
    · -- a second missing computer scientist: add `d`
      by_contra hdc
      refine hmin ⟨insert d S, ⟨⟨y, .inr hyS, hyL⟩, fun h ↦ (h hcC).elim
          (fun h ↦ hdc h.symm) hcS⟩,
        .inr (ssubset_iff_of_subset (fun z (hz : z ∈ S ∩ C) ↦ (⟨.inr hz.1, hz.2⟩ :
          z ∈ insert d S ∩ C)) |>.2
          ⟨d, ⟨.inl rfl, hdC⟩, fun h ↦ hdS h.1⟩), ?_⟩
      rintro (h | h)
      · obtain ⟨z, ⟨hz, hzL⟩, hzS⟩ := exists_of_ssubset h
        exact hz.elim (fun h ↦ hd z hzL (h ▸ hdC)) fun h ↦ hzS ⟨h, hzL⟩
      · exact hdS (h.subset ⟨.inl rfl, hdC⟩).1
  · rintro ⟨⟨l, hl⟩, c, hc⟩
    have hcm : c ∈ C \ S := hc.symm ▸ mem_singleton c
    refine ⟨⟨⟨l, hl.symm ▸ mem_singleton l⟩, fun h ↦ hcm.2 (h hcm.1)⟩,
      fun ⟨v, ⟨hvL, hCv⟩, h, _⟩ ↦ ?_⟩
    rcases h with h | h
    · rw [hl, ssubset_singleton_iff] at h
      exact hvL.ne_empty h
    · refine hCv fun z hzC ↦ ?_
      by_cases hzS : z ∈ S
      · exact (h.subset ⟨hzS, hzC⟩).1
      · obtain ⟨y, ⟨hyv, hyC⟩, hy⟩ := exists_of_ssubset h
        have hyc : y = c := by
          have : y ∈ C \ S := ⟨hyC, fun hyS ↦ hy ⟨hyS, hyC⟩⟩
          rwa [hc] at this
        have hzc : z = c := by
          have : z ∈ C \ S := ⟨hzC, hzS⟩
          rwa [hc] at this
        exact hzc ▸ hyc ▸ hyv

-- p. 70: the hybrid order is not transitive with three linguists and three computer scientists
theorem not_transitive_ltHybrid :
    let r := ltHybrid (fun w : Finset (Fin 6) ↦ (w : Set (Fin 6)))
      (someButNotAll ↑({0, 1, 2} : Finset (Fin 6)) ↑({3, 4, 5} : Finset (Fin 6)))
    r {0, 4} {0, 1, 3, 5} ∧ r {0, 1, 3, 5} {2, 3} ∧ ¬ r {0, 4} {2, 3} := by
  have hLC : Disjoint (↑({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6))
      ↑({3, 4, 5} : Finset (Fin 6)) := Finset.disjoint_coe.2 (by decide)
  have hL : (↑({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6)).Nonempty := ⟨0, by simp⟩
  have hC : (↑({3, 4, 5} : Finset (Fin 6)) : Set (Fin 6)).Nonempty := ⟨3, by simp⟩
  simp only [ltHybrid, leHybrid, ltPos, ltNeg, positiveRestriction_someButNotAll hLC hC,
    negativeRestriction_someButNotAll hLC hL, ← Finset.coe_inter, Finset.coe_ssubset]
  decide

end Examples

/-! ### Spector's favoring (§1.3.2, §2.2.2) -/

section Spector

open Spector2007

variable {Atom : Type*} [DecidableEq Atom] {P : Proposition Atom} {x : Atom}

/-- A proposition of Spector's question-relative language, a set of valuations of the atoms, as a
quantifier over the atoms: it holds of the sets of atoms its valuations make true. -/
def quantifierOf (P : Proposition Atom) : Quantifier Atom := fun S ↦ ∃ V ∈ P, (V : Set Atom) = S

-- p. 67: favoring a positive literal is membership in the positive restriction
theorem favors_pos_iff : Favors P (.pos x) ↔ x ∈ positiveRestriction (quantifierOf P) := by
  rw [mem_positiveRestriction_iff]
  constructor
  · rintro ⟨V, hV, hx, hflip⟩
    refine ⟨V, ⟨V, hV, rfl⟩, fun ⟨V', hV', hV'eq⟩ ↦ hflip ?_⟩
    have hx : x ∈ V := hx
    have : V' = V.erase x := Finset.coe_injective (by rw [hV'eq, Finset.coe_erase])
    rw [show Spector2007.flip V (.pos x) = V.erase x by simp [Spector2007.flip, Literal.atom, hx],
      ← this]
    exact hV'
  · rintro ⟨S, ⟨V, hV, rfl⟩, hS⟩
    have hx : x ∈ V := by_contra fun h ↦ hS ⟨V, hV, by rw [sdiff_singleton_eq_self (by simpa)]⟩
    refine ⟨V, hV, hx, fun h ↦ hS ⟨_, h, ?_⟩⟩
    simp [Spector2007.flip, Literal.atom, hx]

-- p. 67: favoring a negative literal is membership in the negative restriction
theorem favors_neg_iff : Favors P (.neg x) ↔ x ∈ negativeRestriction (quantifierOf P) := by
  rw [mem_negativeRestriction_iff]
  constructor
  · rintro ⟨V, hV, hx, hflip⟩
    refine ⟨V, ⟨V, hV, rfl⟩, fun ⟨V', hV', hV'eq⟩ ↦ hflip ?_⟩
    have hx : x ∉ V := hx
    have : V' = insert x V := Finset.coe_injective (by rw [hV'eq, Finset.coe_insert])
    rw [show Spector2007.flip V (.neg x) = insert x V by simp [Spector2007.flip, Literal.atom, hx],
      ← this]
    exact hV'
  · rintro ⟨S, ⟨V, hV, rfl⟩, hS⟩
    have hx : x ∉ V := fun h ↦ hS ⟨V, hV, by rw [insert_eq_of_mem (by simpa)]⟩
    refine ⟨V, hV, hx, fun h ↦ hS ⟨_, h, ?_⟩⟩
    simp [Spector2007.flip, Literal.atom, hx]

/-- A proposition is quasi-positive in Spector's sense, strongly favoring no negative literal,
just when the quantifier it determines is positively skewed (§2.1.1, after Spector's (77b)). -/
theorem quasiPositive_iff_positivelySkewed :
    (∀ x, ¬ (Favors P (.neg x) ∧ ¬ Favors P (.pos x))) ↔ PositivelySkewed (quantifierOf P) := by
  simp only [positivelySkewed_iff, favors_neg_iff, favors_pos_iff, not_and, not_not]
  rfl

end Spector

end Fagen2026
