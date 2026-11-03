module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Questions.Closure
public import Studies.Dayal2016
public import Linglib.Data.Examples.AlonsoOvalleMoghiseh2025b
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers

/-!
# Alonso-Ovalle and Moghiseh (2025): number marking in Farsi *what* interrogatives

Farsi singular *what* interrogatives, bare (*chi*) and complex (*che ketab-i*), allow singular and
plural answers; with the differential object marker *-ro* only the bare ones do. An interrogative
ranges over the conjunctions and disjunctions of the nonempty subsets of its domain, so [a strongest
true answer exists as soon as some answer is true](##dom_hamblin), whatever the domain's number.
*-ro* restricts those subsets to singletons, [leaving the individuals of the
domain](##hamblinRo_eq_image) and with them Dayal's presupposition: [each interrogative presupposes
what one of Dayal's three does](##Wh.presupposition_eq), and [the free choice disjunctions under
*must* disappear](##Wh.freeChoice_iff). [The paper's answer judgments follow](##rows_agree).

## Implementation notes

* A world is the plurality bought, as in `Dayal2016`, so the distributive *bought* of `x` is
  `Set.Ici x`. The subsets of a domain are finite, as mathlib's closures make them.
* The paper derives no plural interrogative. Without *-ro* a plural phrase here ranges over
  pluralities alone, as the paper reports Maldonado proposing for plural bare interrogatives, and
  `Wh.presupposition` does not let a singular phrase compete with it: with competition in both
  directions the singular phrase would lose its plural answers.
* The free choice answers some informants accept to *-ro* questions under *must* are not fitted: the
  analysis predicts presupposition failure, and the paper takes them to be rejecting it.

## Errata

* (52) requires of every `P` that `f(P)` be a singleton subset of `P`, [which no function does at
  the empty set](##not_exists_forall_ncard_eq_one). `IsSingletonSelection` requires it of nonempty
  sets.
* The paper objects that singular interrogatives over pluralities would not compete with plural
  ones, wrongly admitting singular answers to the latter. [Its own Hamblin sets leave the
  competition equally vacuous](##unblocked_dom_hamblin), so (25) needs the plural domain above,
  while [with *-ro* Dayal's competition returns](##unblocked_dom_hamblinRo) and (28) does not.
* (51) prints *have-to* in the LFs of the non-modal (49)–(50), and (40), (45) and (53) print
  `B[(thing₁,r) ∧ B(thing₂,r)]` for `[B(thing₁,r) ∧ B(thing₂,r)]`.

## TODO

* The *which* interrogatives and the indefinite uses of *what*, which the paper leaves open.

## References

* [alonso-ovalle-moghiseh-2025b]
* [dayal-1996]
* [dayal-2016]
* [hamblin-1973b]
* [maldonado-2020]
* [elliott-nicolae-sauerland-2022]
* [alonso-ovalle-rouillard-2023]
* [scontras-2022]
* [spector-2008]
-/

@[expose] public section

namespace AlonsoOvalleMoghiseh2025b

open Question Set Competition Quantifier Dayal2016
open scoped SetRel

variable {E W : Type*}

/-! ### Hamblin sets over conjunctions and disjunctions -/

section Hamblin

/-- The worlds where ANS (8) is defined on a Hamblin set, the `dom` of EXHp (15). -/
def dom (H : Set (Set W)) : Set W := {w | IsExhaustivelyResolvable H w}

variable (P : E → Set W) (D : Set E)

/-- The Hamblin set (29) of an interrogative with nucleus `P` and domain `D`: the conjunctions and
the disjunctions of `P` over the nonempty subsets of `D`. -/
def hamblin : Set (Set W) := infClosure (P '' D) ∪ supClosure (P '' D)

/-- A subset selection function (48) returns a subset of its argument. -/
def IsSubsetSelection (f : Set E → Set E) : Prop := ∀ A, f A ⊆ A

/-- *-ro* (52) requires a subset selection function to return a singleton of a nonempty set. -/
def IsSingletonSelection (f : Set E → Set E) : Prop :=
  IsSubsetSelection f ∧ ∀ A : Set E, A.Nonempty → ∃ x, f A = {x}

/-- The Hamblin set of the LF (51), closing the selection function that *-ro* restricts. -/
def hamblinRo : Set (Set W) := ⋃ f ∈ {f | IsSingletonSelection f}, hamblin P (f D)

variable {P D} {q : Set W} {w : W}

private theorem mem_hamblin : q ∈ hamblin P D ↔
    ∃ X : Finset E, X.Nonempty ∧ ↑X ⊆ D ∧ (⋂ x ∈ X, P x = q ∨ ⋃ x ∈ X, P x = q) := by
  simp only [hamblin, mem_union, Set.mem_infClosure_image, Set.mem_supClosure_image, ← exists_or,
    ← and_or_left]

-- (29)
theorem mem_hamblin_iff_quantifier : q ∈ hamblin P D ↔
    ∃ X : Finset E, X.Nonempty ∧ ↑X ⊆ D ∧
      ({v | (⨅ x ∈ X, individual x) {y | v ∈ P y}} = q ∨
        {v | (⨆ x ∈ X, individual x) {y | v ∈ P y}} = q) := by
  simp [mem_hamblin, individual, Set.ext_iff]

theorem hamblin_mono {D' : Set E} (h : D' ⊆ D) : hamblin P D' ⊆ hamblin P D :=
  union_subset_union (infClosure_mono (image_mono h)) (supClosure_mono (image_mono h))

-- (58)
@[simp] theorem hamblin_singleton (x : E) : hamblin P {x} = {P x} := by simp [hamblin]

@[simp] theorem hamblin_empty : hamblin P ∅ = ∅ := by simp [hamblin]

theorem subset_biUnion_of_mem_hamblin (hq : q ∈ hamblin P D) : q ⊆ ⋃ x ∈ D, P x := by
  obtain ⟨X, ⟨x, hx⟩, hXD, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact (biInter_subset_of_mem hx).trans (subset_biUnion_of_mem (hXD hx))
  · exact biUnion_subset_biUnion_left hXD

-- (10), (11), (41), (46)
theorem isStrongestTrueAnswer_hamblin (hD : D.Finite) (h : ∃ x ∈ D, w ∈ P x) :
    IsStrongestTrueAnswer (hamblin P D) w (⋂ x ∈ {x ∈ D | w ∈ P x}, P x) := by
  obtain ⟨x₀, hx₀, hw₀⟩ := h
  have hT : {x ∈ D | w ∈ P x}.Finite := hD.subset (sep_subset _ _)
  have hmem : ⋂ x ∈ {x ∈ D | w ∈ P x}, P x ∈ hamblin P D :=
    mem_hamblin.2 ⟨hT.toFinset, ⟨x₀, by simp [hx₀, hw₀]⟩, by simp +contextual [subset_def],
      .inl (by simp)⟩
  refine ⟨⟨hmem, by simp +contextual⟩, fun q ⟨hq, hw⟩ ↦ ?_⟩
  obtain ⟨X, -, hXD, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact subset_iInter₂ fun y hy ↦
      biInter_subset_of_mem (s := {x ∈ D | w ∈ P x}) ⟨hXD hy, mem_iInter₂.1 hw y hy⟩
  · obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.1 hw
    exact (biInter_subset_of_mem (s := {x ∈ D | w ∈ P x}) ⟨hXD hy, hwy⟩).trans
      (subset_biUnion_of_mem hy)

/-- An interrogative over conjunctions and disjunctions presupposes only that some member of its
domain makes the nucleus true: the conjunction over all such members is the strongest true answer,
however many there are. -/
theorem dom_hamblin (hD : D.Finite) : dom (hamblin P D) = ⋃ x ∈ D, P x :=
  Set.ext fun _ ↦ ⟨fun h ↦ let ⟨_, hq, hw⟩ := h.exists_mem; subset_biUnion_of_mem_hamblin hq hw,
    fun h ↦ ⟨_, isStrongestTrueAnswer_hamblin hD (by simpa using h)⟩⟩

variable (P D)

-- fn. 6
theorem biUnion_isSubsetSelection_hamblin :
    ⋃ f ∈ {f | IsSubsetSelection f}, hamblin P (f D) = hamblin P D :=
  subset_antisymm (iUnion₂_subset fun _ hf ↦ hamblin_mono (hf D))
    (subset_biUnion_of_mem (s := {f | IsSubsetSelection f}) (u := fun f ↦ hamblin P (f D))
      (x := id) fun _ ↦ subset_rfl)

-- (52) as printed
theorem not_exists_forall_ncard_eq_one : ¬ ∃ f : Set E → Set E, ∀ A, f A ⊆ A ∧ (f A).ncard = 1 :=
  fun ⟨f, hf⟩ ↦ by simpa [subset_empty_iff.1 (hf ∅).1] using (hf ∅).2

/-- *-ro* reduces an interrogative's Hamblin set to the individuals of its domain: a singleton
subset selects one individual, over which conjunction and disjunction coincide. -/
theorem hamblinRo_eq_image : hamblinRo P D = P '' D := by
  classical
  ext q
  simp only [hamblinRo, mem_iUnion, exists_prop, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨f, hf, hq⟩
    rcases D.eq_empty_or_nonempty with rfl | hD
    · rw [subset_empty_iff.1 (hf.1 ∅), hamblin_empty] at hq
      exact hq.elim
    · obtain ⟨x, hx⟩ := hf.2 D hD
      rw [hx, hamblin_singleton] at hq
      exact ⟨x, hf.1 D (hx ▸ rfl), hq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun A ↦ if x ∈ A then {x} else if h : A.Nonempty then {h.some} else ∅,
      ⟨fun A ↦ ?_, fun A hA ↦ ?_⟩, by simp [hx]⟩
    · dsimp only
      split_ifs with h h'
      exacts [singleton_subset_iff.2 h, singleton_subset_iff.2 h'.some_mem, empty_subset _]
    · dsimp only
      split_ifs
      exacts [⟨_, rfl⟩, ⟨_, rfl⟩]

end Hamblin

/-! ### Number -/

section Number

variable [CompleteLattice E] {a b w : E}

theorem exists_mem_domain_le [Finite E] (n : Option Number) (hw : w ≠ ⊥) : ∃ x ∈ domain n, x ≤ w :=
  let ⟨a, ha, haw⟩ := (eq_bot_or_exists_atom_le w).resolve_left hw
  ⟨a, mem_domain_of_isAtom n ha, haw⟩

theorem dom_hamblin_domain [Finite E] (n : Option Number) :
    dom (hamblin Ici (domain n)) = {w : E | w ≠ ⊥} := by
  rw [dom_hamblin (toFinite _)]
  refine Set.ext fun w ↦ ⟨fun h ↦ ?_, fun hw ↦ ?_⟩
  · rintro rfl
    obtain ⟨x, hx, hxw⟩ := mem_iUnion₂.1 h
    exact hx.2 (le_bot_iff.1 hxw)
  · obtain ⟨x, hx, hxw⟩ := exists_mem_domain_le n hw
    exact mem_biUnion hx hxw

-- (40), (45), (46): the answer to a plural world, even over atoms, is the conjunction of its parts
theorem dayalAns_hamblin_domain [IsAtomistic E] [Finite E] (n : Option Number) (hw : w ≠ ⊥) :
    dayalAns (hamblin Ici (domain n)) w = some (Ici w) := by
  have h := isStrongestTrueAnswer_hamblin (P := Ici) (toFinite (domain n))
    (exists_mem_domain_le n hw)
  rwa [show ⋂ x ∈ {x ∈ domain n | w ∈ Ici x}, Ici x = Ici w by
    rw [← Ici_sSup]
    exact congrArg Ici (sSup_domain_le n w), ← dayalAns_eq_some_iff] at h

-- p. 8: the objection to singular interrogatives over pluralities, against (29)
theorem unblocked_dom_hamblin [Finite E] (n : Option Number) :
    unblocked numberAlts (fun m ↦ dom (hamblin Ici (domain m))) n = {w : E | w ≠ ⊥} := by
  simp only [dom_hamblin_domain]
  exact unblocked_eq_self fun ⟨_, _, h⟩ ↦ h.ne rfl

-- (26)–(28), (53), (55): with *-ro*, Dayal's domains and competition
theorem unblocked_dom_hamblinRo (n : Option Number) :
    unblocked numberAlts (fun m ↦ dom (hamblinRo Ici (domain m))) n = felicitous (E := E) n := by
  simp only [hamblinRo_eq_image]
  rfl

/-- The pluralities, the domain of a plural interrogative phrase without *-ro*. -/
def pluralities : Set E := {x | x ≠ ⊥ ∧ ¬ IsAtom x}

theorem isUpperSet_pluralities : IsUpperSet (pluralities : Set E) :=
  fun _ _ hxy ⟨hx, hna⟩ ↦ ⟨fun h ↦ hx (le_bot_iff.1 (h ▸ hxy)),
    fun hy ↦ hna ((hy.le_iff_eq hx).1 hxy ▸ hy)⟩

-- (21), (25)
theorem dom_hamblin_pluralities [Finite E] :
    dom (hamblin Ici pluralities) = (pluralities : Set E) := by
  rw [dom_hamblin (toFinite _)]
  exact Set.ext fun w ↦ ⟨fun h ↦ let ⟨_, hx, hxw⟩ := mem_iUnion₂.1 h; isUpperSet_pluralities hxw hx,
    fun hw ↦ mem_biUnion hw self_mem_Ici⟩

private theorem not_isAtom_sup (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) : ¬ IsAtom (a ⊔ b) :=
  fun h ↦ hab (((h.le_iff_eq ha.ne_bot).1 le_sup_left).trans
    ((h.le_iff_eq hb.ne_bot).1 le_sup_right).symm)

private theorem sup_ne_bot (ha : IsAtom a) : a ⊔ b ≠ ⊥ :=
  fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1

theorem sup_mem_domain_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (n : Option Number) :
    a ⊔ b ∈ domain n ↔ n ≠ some .singular := by
  by_cases hn : n = some .singular
  · simp [hn, mem_domain_singular, not_isAtom_sup ha hb hab]
  · simp [hn, domain_of_ne_singular hn, sup_ne_bot ha]

variable [IsAtomistic E]

theorem atom_mem_felicitous_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (n : Option Number) :
    a ∈ felicitous n ↔ n = none ∨ n = some .singular := by
  rcases n with _ | m
  · simp [felicitous_none, ha.ne_bot]
  · by_cases hm : m = .singular
    · simp [hm, felicitous_singular, ha]
    · simp [felicitous_of_ne_singular ha hb hab hm, ha, hm]

theorem sup_mem_felicitous_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (n : Option Number) :
    a ⊔ b ∈ felicitous n ↔ n ≠ some .singular := by
  rcases n with _ | m
  · simp [felicitous_none, sup_ne_bot ha]
  · by_cases hm : m = .singular
    · simp [hm, felicitous_singular, not_isAtom_sup ha hb hab]
    · simp [felicitous_of_ne_singular ha hb hab hm, sup_ne_bot ha, not_isAtom_sup ha hb hab, hm]

end Number

/-! ### The interrogatives -/

/-- What an interrogative phrase ranges over. -/
inductive Wh
  /-- The individuals of a number, as on Dayal's analysis and, by `hamblinRo_eq_image`, with
  *-ro*. -/
  | individuals (n : Option Number)
  /-- The conjunctions and disjunctions (29) over the individuals of a number. -/
  | quantifiers (n : Option Number)
  /-- The conjunctions and disjunctions over pluralities. -/
  | plural
  deriving DecidableEq

namespace Wh

variable [CompleteLattice E] {a b : E}

/-- The Hamblin set of an interrogative whose nucleus is distributive. -/
def hamblinSet : Wh → Set (Set E)
  | .individuals n => Dayal2016.hamblin n
  | .quantifiers n => AlonsoOvalleMoghiseh2025b.hamblin Ici (domain n)
  | .plural => AlonsoOvalleMoghiseh2025b.hamblin Ici pluralities

/-- The worlds where an interrogative's question is defined: ANS (8), under the competition of
EXHp (15) when it ranges over individuals, whose condition is `Competition.unblocked`. -/
def presupposition : Wh → Set E
  | .individuals n => felicitous n
  | i => dom i.hamblinSet

/-- The number whose individuals, on Dayal's analysis, an interrogative's presupposition matches. -/
def pattern : Wh → Option Number
  | .individuals n => n
  | .quantifiers _ => none
  | .plural => some .plural

/-- Each interrogative presupposes what one of Dayal's three does: conjunctions and disjunctions
make a singular phrase pattern with a bare one, *-ro* restores the singular, and a plural phrase
stays plural. -/
theorem presupposition_eq [IsAtomistic E] [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ∀ i : Wh, (i.presupposition : Set E) = felicitous i.pattern
  | .individuals _ => rfl
  | .quantifiers n => (dom_hamblin_domain n).trans felicitous_none.symm
  | .plural => dom_hamblin_pluralities.trans (felicitous_plural ha hb hab).symm

/-- Whether an interrogative ranges over disjunctions of individuals. -/
def freeChoice : Wh → Bool
  | .quantifiers _ => true
  | _ => false

end Wh

/-! ### Questions with *must* -/

section Must

/-- The accessibility of *must*, from a deontic state to the worlds it permits. -/
def permits : SetRel (Set E) E := .ofSuccessors id

theorem permits_singleton (v : E) : ∃ A : Set E, ∀ u, A ~[permits] u ↔ u = v :=
  ⟨{v}, fun _ ↦ Iff.rfl⟩

variable [CompleteLattice E] {a b : E} {D s : Set E}

private theorem eq_of_le_atom {x c : E} (hD : ⊥ ∉ D) (hx : x ∈ D) (hc : IsAtom c) (hxc : x ≤ c) :
    x = c :=
  (hc.le_iff_eq (ne_of_mem_of_not_mem hx hD)).1 hxc

-- (34)–(36): the free choice disjunction answers the question in the scenario (59)
theorem isLeast_supported_hamblin (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (haD : a ∈ D)
    (hbD : b ∈ D) (hD : ⊥ ∉ D) (has : a ∈ s) (hbs : b ∈ s) (hs : s ⊆ Ici a ∪ Ici b) :
    IsLeast (supported (hamblin Ici D) s) (Ici a ∪ Ici b) := by
  refine ⟨⟨.inr (sup_mem_supClosure (mem_image_of_mem _ haD) (mem_image_of_mem _ hbD)), hs⟩, ?_⟩
  rintro q ⟨hq, hsq⟩
  obtain ⟨X, ⟨x, hx⟩, hXD, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact (hab ((eq_of_le_atom hD (hXD hx) ha (mem_iInter₂.1 (hsq has) x hx)).symm.trans
      (eq_of_le_atom hD (hXD hx) hb (mem_iInter₂.1 (hsq hbs) x hx)))).elim
  · have mem {c : E} (hc : IsAtom c) (hcs : c ∈ s) : c ∈ X :=
      let ⟨_, hy, hyc⟩ := mem_iUnion₂.1 (hsq hcs); eq_of_le_atom hD (hXD hy) hc hyc ▸ hy
    exact union_subset (subset_biUnion_of_mem (mem ha has)) (subset_biUnion_of_mem (mem hb hbs))

-- (32), (33), (62), (63): over individuals, *must* requires a particular individual
theorem not_isExhaustivelyResolvableOn_image_Ici (hab : a ≠ b) (ha : IsAtom a) (hb : IsAtom b)
    (hD : ⊥ ∉ D) (has : a ∈ s) (hbs : b ∈ s) : ¬ IsExhaustivelyResolvableOn (Ici '' D) s := by
  rintro ⟨_, ⟨⟨x, hx, rfl⟩, hxs⟩, -⟩
  exact hab ((eq_of_le_atom hD hx ha (hxs has)).symm.trans (eq_of_le_atom hD hx hb (hxs hbs)))

/-- In a scenario where *must* requires one of two things and permits buying either alone, a
question under *must* is defined exactly when its phrase ranges over disjunctions of individuals,
with the free choice disjunction as its answer. Individuals, and so *-ro*, demand a particular
thing, and pluralities a particular group. -/
theorem Wh.freeChoice_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (has : a ∈ s) (hbs : b ∈ s)
    (hs : s ⊆ Ici a ∪ Ici b) (i : Wh) :
    IsExhaustivelyResolvable (box i.hamblinSet permits) s ↔ i.freeChoice = true := by
  rw [isExhaustivelyResolvable_box_iff _ permits_singleton (x := s) (s := s) fun _ ↦ Iff.rfl]
  cases i with
  | individuals n =>
    exact iff_of_false
      (not_isExhaustivelyResolvableOn_image_Ici hab ha hb (fun h ↦ h.2 rfl) has hbs)
      Bool.false_ne_true
  | quantifiers n =>
    exact iff_of_true ⟨_, isLeast_supported_hamblin ha hb hab (mem_domain_of_isAtom n ha)
      (mem_domain_of_isAtom n hb) (fun h ↦ h.2 rfl) has hbs hs⟩ rfl
  | plural =>
    refine iff_of_false ?_ Bool.false_ne_true
    rintro ⟨q, ⟨hq, hsq⟩, -⟩
    obtain ⟨x, hx, hxa⟩ := mem_iUnion₂.1 (subset_biUnion_of_mem_hamblin hq (hsq has))
    exact (isUpperSet_pluralities hxa hx).2 ha

end Must

/-! ### Collective predicates -/

section Collective

variable [CompleteLattice E] {a b : E}

/-- *Mix together*, a collective predicate true in a world of the pluralities bought in it. -/
def mixed (x : E) : Set E := {w | x ≤ w ∧ ¬ IsAtom x}

-- (56), (57)
theorem nonempty_dom_hamblin_mixed_iff [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (n : Option Number) :
    (dom (hamblin mixed (domain n)) : Set E).Nonempty ↔ n ≠ some .singular := by
  rw [dom_hamblin (toFinite _)]
  refine ⟨?_, fun hn ↦ ⟨a ⊔ b, mem_biUnion ((sup_mem_domain_iff ha hb hab n).2 hn)
    ⟨le_rfl, not_isAtom_sup ha hb hab⟩⟩⟩
  rintro ⟨w, h⟩ rfl
  obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 h
  exact hwx.2 (mem_domain_singular.1 hx)

-- (56), (57)
theorem nonempty_dom_hamblinRo_mixed_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    (n : Option Number) :
    (dom (hamblinRo mixed (domain n)) : Set E).Nonempty ↔ n ≠ some .singular := by
  rw [hamblinRo_eq_image]
  refine ⟨?_, fun hn ↦ ⟨a ⊔ b, mixed (a ⊔ b), ⟨⟨_, (sup_mem_domain_iff ha hb hab n).2 hn, rfl⟩,
    le_rfl, not_isAtom_sup ha hb hab⟩, ?_⟩⟩
  · rintro ⟨w, h⟩ rfl
    obtain ⟨_, ⟨x, hx, rfl⟩, hwx⟩ := h.exists_mem
    exact hwx.2 (mem_domain_singular.1 hx)
  · rintro _ ⟨⟨x, -, rfl⟩, hxw, hx⟩
    exact fun v hv ↦ ⟨hxw.trans hv.1, hx⟩

end Collective

/-! ### The paper's judgments -/

/-- The interrogative of a row, by its language, its type in the paper's taxonomy, and whether it
carries *-ro*. -/
def wh? (e : Datum) : Option Wh :=
  (e.byLanguage [
    (.english, [("BI", .individuals none), ("SCI", .individuals (some .singular)),
      ("PCI", .individuals (some .plural))]),
    (.spanish, [("SBI", .quantifiers (some .singular)), ("PBI", .plural),
      ("SCI", .individuals (some .singular)), ("PCI", .individuals (some .plural))]),
    (.westernFarsi, if "ro" ∈ e.surfaceTokens then
      [("SBI", .individuals none), ("SCI", .individuals (some .singular)),
        ("PCI", .individuals (some .plural))]
    else
      [("SBI", .quantifiers none), ("SCI", .quantifiers (some .singular)), ("PBI", .plural),
        ("PCI", .plural)])]).bind (e.parse? "type")

/-- The judgment of a row's reading whose name begins with `pre`. -/
def reading? (e : Datum) (pre : String) : Option Judgment :=
  (e.readings.find? fun r ↦ pre.toList.isPrefixOf r.1.toList).map Prod.snd

/-- A row's interrogative, where the paper judges its singular and plural answers. -/
def answers? (e : Datum) : Option Wh := (wh? e).filter fun _ ↦ (reading? e "singular").isSome

/-- A row's singular answer is accepted exactly when its interrogative's presupposition holds in a
world where one atom was bought, and its plural answer when it holds where two were. -/
theorem rows_agree [CompleteLattice E] [IsAtomistic E] [Finite E] {a b : E} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : ∀ e ∈ Examples.all, ∀ i ∈ answers? e,
      (a ∈ i.presupposition ↔ reading? e "singular" = some .acceptable) ∧
        (a ⊔ b ∈ i.presupposition ↔ reading? e "plural" = some .acceptable) := by
  simp only [Wh.presupposition_eq ha hb hab, atom_mem_felicitous_iff ha hb hab,
    sup_mem_felicitous_iff ha hb hab]
  decide +kernel

example : Datum.ReadCount answers? Examples.all 14 := by decide +kernel

example := rows_agree (E := Set (Fin 2)) (Set.isAtom_singleton 0) (Set.isAtom_singleton 1) (by simp)

-- (60)–(63)
theorem scenario_rows : Datum.ChecksVerdict wh? Wh.freeChoice Examples.all 4 := by decide +kernel

example := Wh.freeChoice_iff (E := Set (Fin 2)) (a := {0}) (b := {1}) (s := {{0}, {1}})
  (Set.isAtom_singleton 0) (Set.isAtom_singleton 1) (by simp) (by simp) (by simp)
  (by rintro _ (rfl | rfl) <;> simp)

/-- A row's interrogative, where a free choice answer answers it. -/
def freeChoiceAnswer? (e : Datum) : Option Wh :=
  (wh? e).filter fun i ↦ i.freeChoice ∧ (reading? e "free choice").isSome

-- (30), (31)
theorem freeChoiceAnswer_rows : ∀ e ∈ Examples.all, ∀ _ ∈ freeChoiceAnswer? e,
    reading? e "free choice" = some .acceptable := by decide +kernel

example : Datum.ReadCount freeChoiceAnswer? Examples.all 2 := by decide +kernel

/-- A row's number, where it combines *baham* 'together' with a collective predicate. -/
def collective? (e : Datum) : Option (Option Number) :=
  if "baham" ∈ e.surfaceTokens then e.parse? "type" [("SBI", none), ("SCI", some .singular)]
  else none

-- (56), (57), each with or without *-ro*
theorem collective_rows [CompleteLattice E] [Finite E] {a b : E} (ha : IsAtom a) (hb : IsAtom b)
    (hab : a ≠ b) : ∀ e ∈ Examples.all, ∀ n ∈ collective? e,
      ((dom (hamblin mixed (domain n)) : Set E).Nonempty ↔ e.judgment = .acceptable) ∧
        ((dom (hamblinRo mixed (domain n)) : Set E).Nonempty ↔ e.judgment = .acceptable) := by
  simp only [nonempty_dom_hamblin_mixed_iff ha hb hab, nonempty_dom_hamblinRo_mixed_iff ha hb hab]
  decide +kernel

example : Datum.ReadCount collective? Examples.all 2 := by decide +kernel

end AlonsoOvalleMoghiseh2025b
