module

public import Linglib.Semantics.Plurality.Number
public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Questions.Closure
public import Linglib.Semantics.Questions.Number
public import Linglib.Data.Examples.AlonsoOvalleMoghiseh2025b
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers

/-!
# Alonso-Ovalle and Moghiseh (2025): number marking in Farsi *what* interrogatives

Farsi singular *what* interrogatives, bare (*chi*) and complex (*che ketab-i*), allow singular and
plural answers; with the differential object marker *-ro* only the bare ones do. An interrogative
ranges over the conjunctions and disjunctions of the nonempty subsets of its domain, so [it
presupposes only that some answer is true](##Question.presupposition_hamblin), whatever the domain's
number. *-ro* restricts those subsets to singletons, [leaving the individuals of the
domain](##hamblinRo_eq_image), with Dayal's presupposition. [Each interrogative is then felicitous
on one of three domains](##Range.felicitous_eq), and [the free choice disjunctions under *must*
disappear](##Range.freeChoice_iff). [The paper's answer judgments follow](##rows_agree).

## Implementation notes

* A world is the plurality bought, so the distributive *bought* of `x` is `Set.Ici x`. The subsets
  of a domain are finite, as mathlib's closures make them.
* The paper gives no LF for its plural interrogatives. Without *-ro* a plural phrase here ranges
  over pluralities alone, the higher-order extension of Maldonado's strong plural by Alonso-Ovalle
  and Rouillard, which the paper endorses for bare phrases; extending it to complex phrases is this
  file's choice. Competition in number applies only over individuals: [obligatory competition
  over conjunctions and disjunctions would cost a singular phrase its plural
  answers](##strengthen_hamblin_domain_singular), as those authors observe.
* The free choice answers some informants accept to *-ro* questions under *must* are not fitted: the
  analysis predicts presupposition failure, and the paper takes them to be rejecting it.
* The paper's taxonomy of interrogatives stays a row feature, since no theory-layer type of *wh*
  phrase exists for a Farsi fragment entry to instantiate.

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

open Question Set Presupposition Quantifier
open scoped SetRel

variable {E W : Type*}

/-! ### Hamblin sets over conjunctions and disjunctions -/

section Hamblin

variable (P : E → Set W) (D : Set E)

/-- A subset selection function (48) returns a subset of its argument. -/
def IsSubsetSelection (f : Set E → Set E) : Prop := ∀ A, f A ⊆ A

/-- *-ro* (52) requires a subset selection function to return a singleton of a nonempty set. -/
def IsSingletonSelection (f : Set E → Set E) : Prop :=
  IsSubsetSelection f ∧ ∀ A : Set E, A.Nonempty → ∃ x, f A = {x}

/-- The Hamblin set of the LF (51), closing the selection function that *-ro* restricts. -/
def hamblinRo : Set (Set W) := ⋃ f ∈ {f | IsSingletonSelection f}, hamblin P (f D)

variable {P D} {q : Set W} {w : W}

-- (29)
theorem mem_hamblin_iff_quantifier : q ∈ hamblin P D ↔
    ∃ X : Finset E, X.Nonempty ∧ ↑X ⊆ D ∧
      ({v | (⨅ x ∈ X, individual x) {y | v ∈ P y}} = q ∨
        {v | (⨆ x ∈ X, individual x) {y | v ∈ P y}} = q) := by
  simp [mem_hamblin, individual, Set.ext_iff]

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

/-! ### Number and competition -/

section Number

/-- The number marking of an interrogative phrase. -/
inductive Marking
  /-- No semantic number, as the root (37) of a singular bare phrase or an English bare phrase. -/
  | neutral
  /-- SING (42), of a singular complex phrase. -/
  | singular
  /-- Plural marking. -/
  | plural
  deriving DecidableEq

/-- The number of Dayal's domain that a marking carries. -/
def Marking.number : Marking → Option Number
  | .neutral => none
  | .singular => some .singular
  | .plural => some .plural

/-- What an interrogative phrase ranges over. -/
inductive Range
  /-- The individuals of Dayal's domains (9), (12), (14). -/
  | individuals
  /-- The conjunctions and disjunctions (29) over a marked domain. -/
  | quantifiers
  /-- The same over singletons, with *-ro* (51). -/
  | singletons
  deriving DecidableEq

/-- The marking whose domain a phrase presupposes: its own, except that a singular phrase over
quantifiers patterns with a neutral one. -/
def Range.pattern : Range → Marking → Marking
  | .quantifiers, .singular => .neutral
  | _, m => m

variable [CompleteLattice E] {w : E}

/-- The domain a marked phrase ranges over, `[−atomic]` of the non-null individuals when plural. -/
def Marking.domain : Marking → Set E
  | .neutral => whDomain none
  | .singular => whDomain (some .singular)
  | .plural => whStrongPlural

/-- The Hamblin set of a phrase whose nucleus is distributive. -/
def Range.hamblinSet : Range → Marking → Set (Set E)
  | .individuals, m => Ici '' whDomain m.number
  | .quantifiers, m => hamblin Ici m.domain
  | .singletons, m => hamblinRo Ici m.domain

/-- The worlds where a question is defined: ANS (8), under the competition of EXHp (15) when the
phrase ranges over individuals. -/
def Range.felicitous : Range → Marking → Set E
  | .individuals, m => whFelicitous m.number
  | r, m => presupposition (r.hamblinSet m)

theorem bot_notMem_domain (m : Marking) : (⊥ : E) ∉ m.domain := by
  cases m <;> simp [Marking.domain, whDomain, mem_whStrongPlural]

theorem Marking.atom_mem_domain_iff {a : E} (ha : IsAtom a) (m : Marking) :
    a ∈ m.domain ↔ m ≠ .plural := by
  cases m <;> simp [Marking.domain, mem_whStrongPlural, ha, mem_whDomain_of_isAtom]

theorem domain_neutral : Marking.domain .neutral = {x : E | x ≠ ⊥} :=
  whDomain_of_ne_singular (by simp)

theorem presupposition_hamblinRo_domain [IsAtomistic E] (m : Marking) :
    presupposition (hamblinRo Ici m.domain) = (m.domain : Set E) := by
  rw [hamblinRo_eq_image]
  cases m
  · exact presupposition_whHamblin none
  · exact presupposition_whHamblin (some .singular)
  · exact presupposition_image_Ici isUpperSet_whStrongPlural

section Finite

variable [Finite E]

-- (21), (25), (40), (45)
theorem presupposition_hamblin_domain (m : Marking) :
    presupposition (hamblin Ici m.domain) = ((Range.pattern .quantifiers m).domain : Set E) := by
  cases m
  · exact (presupposition_hamblin_whDomain none).trans domain_neutral.symm
  · exact (presupposition_hamblin_whDomain (some .singular)).trans domain_neutral.symm
  · exact presupposition_hamblin_Ici (toFinite _) isUpperSet_whStrongPlural

-- (40), (45), (46): the answer to a plural world, even over atoms, is the conjunction of its parts
theorem dayalAns_hamblin_whDomain [IsAtomistic E] (n : Option Number) (hw : w ≠ ⊥) :
    dayalAns (hamblin Ici (whDomain n)) w = some (Ici w) := by
  have h := isStrongestTrueAnswer_hamblin (P := Ici) (toFinite (whDomain n))
    (exists_mem_whDomain_le n hw)
  rwa [show ⋂ x ∈ {x ∈ whDomain n | w ∈ Ici x}, Ici x = Ici w by
    rw [← Ici_sSup]
    exact congrArg Ici (sSup_whDomain_le n w), ← dayalAns_eq_some_iff] at h

-- p. 8: the objection to singular interrogatives over pluralities, against (29)
theorem strengthen_hamblin_whDomain (alts : Option Number → Set (Option Number))
    (n : Option Number) :
    strengthen alts (fun m ↦ presupposition (hamblin Ici (whDomain m))) n = {w : E | w ≠ ⊥} := by
  simp only [presupposition_hamblin_whDomain]
  exact strengthen_eq_self fun _ _ h ↦ h.ne rfl

-- (23): [alonso-ovalle-rouillard-2023] p. 294, EXHp "cannot be obligatory" with a weak singular,
-- which would convey uniqueness; this is the pointwise form, not competition in a context
theorem strengthen_hamblin_domain_singular {a : E} (ha : IsAtom a) :
    strengthen (fun _ ↦ {.singular, .plural}) (fun m ↦ presupposition (hamblin Ici m.domain))
      Marking.singular = {w : E | IsAtom w} := by
  have hsg : presupposition (hamblin Ici Marking.singular.domain) = {w : E | w ≠ ⊥} :=
    (presupposition_hamblin_domain .singular).trans domain_neutral
  have hpl := presupposition_hamblin_domain (E := E) .plural
  refine (strengthen_eq_sdiff (ψ := .plural) (by simp) ?_ ?_).trans ?_
  · rw [hsg, hpl]
    exact ⟨fun _ hw ↦ (mem_whStrongPlural.1 hw).1,
      fun h ↦ (mem_whStrongPlural.1 (h ha.ne_bot)).2 ha⟩
  · rintro χ (rfl | rfl) hχ
    · exact absurd hχ (ssubset_irrefl _)
    · exact subset_rfl
  · rw [hsg, hpl]
    exact Set.ext fun w ↦ ⟨fun ⟨h, hn⟩ ↦ by_contra fun hna ↦
      hn (mem_whStrongPlural.2 ⟨h, hna⟩),
      fun h ↦ ⟨h.ne_bot, fun hp ↦ (mem_whStrongPlural.1 hp).2 h⟩⟩

end Finite

-- (28): *-ro* restores Dayal's domains and competition
theorem strengthen_hamblinRo_whDomain (n : Option Number) :
    strengthen Number.alts (fun m ↦ presupposition (hamblinRo Ici (whDomain m))) n =
      whFelicitous (E := E) n := by
  simp only [hamblinRo_eq_image]
  rfl

end Number

/-! ### Two things -/

section Atoms

variable [CompleteLattice E] {a b : E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)

include ha hb hab

private theorem not_isAtom_sup : ¬ IsAtom (a ⊔ b) :=
  fun h ↦ hab (((h.le_iff_eq ha.ne_bot).1 le_sup_left).trans
    ((h.le_iff_eq hb.ne_bot).1 le_sup_right).symm)

theorem Marking.sup_mem_domain_iff (m : Marking) : a ⊔ b ∈ m.domain ↔ m ≠ .singular := by
  have hne : a ⊔ b ≠ ⊥ := fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1
  have hna := not_isAtom_sup ha hb hab
  cases m <;> simp [Marking.domain, mem_whStrongPlural, hne, hna, mem_whDomain_singular,
    whDomain_of_ne_singular]

variable [IsAtomistic E]

-- each marking's domain is where Dayal's question of that number is felicitous
theorem Marking.whFelicitous_number (m : Marking) : whFelicitous m.number = (m.domain : Set E) := by
  cases m
  · exact whFelicitous_none.trans domain_neutral.symm
  · exact whFelicitous_singular.trans (Set.ext fun _ ↦ mem_whDomain_singular.symm)
  · exact (whFelicitous_plural ha hb hab).trans (Set.ext fun _ ↦ mem_whStrongPlural.symm)

/-- Each interrogative is felicitous on the domain of its pattern. Conjunctions and disjunctions
make a singular phrase pattern with a neutral one, *-ro* restores the singular, and a plural phrase
stays plural. -/
theorem Range.felicitous_eq [Finite E] (r : Range) (m : Marking) :
    (r.felicitous m : Set E) = (r.pattern m).domain := by
  cases r
  · exact Marking.whFelicitous_number ha hb hab m
  · exact presupposition_hamblin_domain m
  · exact presupposition_hamblinRo_domain m

end Atoms

/-! ### Questions with *must* -/

section Must

/-- The accessibility of *must*, from a deontic state to the worlds it permits. -/
def permits : SetRel (Set E) E := .ofSuccessors id

theorem permits_singleton (v : E) : ∃ A : Set E, ∀ u, A ~[permits] u ↔ u = v :=
  ⟨{v}, fun _ ↦ Iff.rfl⟩

variable [CompleteLattice E] {a b : E} {D s : Set E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
  (has : a ∈ s) (hbs : b ∈ s)

include ha hb hab has hbs

-- (32)–(36), (59), (62), (63)
/-- In a scenario where *must* requires one of two things and permits buying either alone, a
question under *must* is defined exactly when its phrase ranges over disjunctions of individuals,
with the free choice disjunction as its answer. Individuals, and so *-ro*, demand a particular
thing, and disjunctions of pluralities are false where one thing alone was bought. -/
theorem Range.freeChoice_iff (hs : s ⊆ Ici a ∪ Ici b) (r : Range) (m : Marking) :
    IsExhaustivelyResolvable (box (r.hamblinSet m) permits) s ↔
      r = .quantifiers ∧ m ≠ .plural := by
  rw [isExhaustivelyResolvable_box_iff _ permits_singleton (x := s) (s := s) fun _ ↦ Iff.rfl]
  have hdis := ha.disjoint_of_ne hb hab
  have atoms {m : Marking} (hm : m ≠ .plural) :
      IsExhaustivelyResolvableOn (hamblin Ici m.domain) s :=
    ⟨_, isLeast_supported_hamblin_pair ((Marking.atom_mem_domain_iff ha m).2 hm)
      ((Marking.atom_mem_domain_iff hb m).2 hm) has hbs hs⟩
  cases r with
  | individuals =>
    exact iff_of_false (not_isExhaustivelyResolvableOn_image_Ici (fun h ↦ h.2 rfl) hdis has hbs)
      (by simp)
  | singletons =>
    simp only [hamblinSet, hamblinRo_eq_image, reduceCtorEq, false_and, iff_false]
    exact not_isExhaustivelyResolvableOn_image_Ici (bot_notMem_domain m) hdis has hbs
  | quantifiers =>
    cases m
    · exact iff_of_true (atoms (by simp)) (by simp)
    · exact iff_of_true (atoms (by simp)) (by simp)
    · refine iff_of_false ?_ (by simp)
      rintro ⟨q, ⟨hq, hsq⟩, -⟩
      obtain ⟨x, hx, hxa⟩ := mem_iUnion₂.1 (subset_biUnion_of_mem_hamblin hq (hsq has))
      exact (mem_whStrongPlural.1 (isUpperSet_whStrongPlural hxa hx)).2 ha

end Must

/-! ### Collective predicates -/

section Collective

variable [CompleteLattice E] {a b : E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)

/-- *Mix together*, a collective predicate true in a world of the pluralities bought in it. -/
def mixed (x : E) : Set E := {w | x ≤ w ∧ ¬ IsAtom x}

include ha hb hab

-- (56), (57)
theorem nonempty_presupposition_hamblin_mixed_iff [Finite E] (m : Marking) :
    (presupposition (hamblin mixed m.domain) : Set E).Nonempty ↔ m ≠ .singular := by
  rw [presupposition_hamblin (toFinite _)]
  refine ⟨?_, fun hm ↦ ⟨a ⊔ b, mem_biUnion ((Marking.sup_mem_domain_iff ha hb hab m).2 hm)
    ⟨le_rfl, not_isAtom_sup ha hb hab⟩⟩⟩
  rintro ⟨w, h⟩ rfl
  obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 h
  exact hwx.2 (mem_whDomain_singular.1 hx)

-- (56), (57)
theorem nonempty_presupposition_hamblinRo_mixed_iff (m : Marking) :
    (presupposition (hamblinRo mixed m.domain) : Set E).Nonempty ↔ m ≠ .singular := by
  rw [hamblinRo_eq_image]
  refine ⟨?_, fun hm ↦ ⟨a ⊔ b, mixed (a ⊔ b),
    ⟨⟨_, (Marking.sup_mem_domain_iff ha hb hab m).2 hm, rfl⟩, le_rfl, not_isAtom_sup ha hb hab⟩,
    ?_⟩⟩
  · rintro ⟨w, h⟩ rfl
    obtain ⟨_, ⟨x, hx, rfl⟩, hwx⟩ := h.exists_mem
    exact hwx.2 (mem_whDomain_singular.1 hx)
  · rintro _ ⟨⟨x, -, rfl⟩, hxw, hx⟩
    exact fun v hv ↦ ⟨hxw.trans hv.1, hx⟩

end Collective

/-! ### The paper's judgments -/

/-- The marking of a row's interrogative phrase, by its type in the paper's taxonomy. -/
def marking? (e : Datum) : Option Marking :=
  e.parse? "type" [("BI", .neutral), ("SBI", .neutral), ("SCI", .singular), ("PBI", .plural),
    ("PCI", .plural)]

/-- What a row's interrogative phrase ranges over: individuals in English and in Spanish complex
phrases, otherwise quantifiers, or singletons with *-ro*. -/
def range? (e : Datum) : Option Range :=
  e.byLanguage [(.english, .individuals),
    (.spanish, if e.feature? "type" ∈ [some "SBI", some "PBI"] then .quantifiers else .individuals),
    (.westernFarsi, if "ro" ∈ e.surfaceTokens then .singletons else .quantifiers)]

/-- A row's interrogative. -/
def wh? (e : Datum) : Option (Range × Marking) := do
  pure (← range? e, ← marking? e)

/-- A row's interrogative, where the paper judges its singular and plural answers. -/
def answers? (e : Datum) : Option (Range × Marking) :=
  (wh? e).filter fun _ ↦ (e.readings.lookup "singular answer").isSome

variable [CompleteLattice E] {a b : E} {s : Set E}

/-- A row's singular answer is accepted exactly when its interrogative is felicitous in a world
where one atom was bought, and its plural answer when it is felicitous where two were. -/
theorem rows_agree [IsAtomistic E] [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ∀ e ∈ Examples.all, ∀ i ∈ answers? e,
      (a ∈ i.1.felicitous i.2 ↔ e.readings.lookup "singular answer" = some .acceptable) ∧
        (a ⊔ b ∈ i.1.felicitous i.2 ↔ e.readings.lookup "plural answer" = some .acceptable) := by
  simp only [Range.felicitous_eq ha hb hab, Marking.atom_mem_domain_iff ha,
    Marking.sup_mem_domain_iff ha hb hab]
  decide +kernel

example : Datum.ReadCount answers? Examples.all 14 := by decide +kernel

example := rows_agree (E := Set (Fin 2)) (Set.isAtom_singleton 0) (Set.isAtom_singleton 1) (by simp)

-- (60)–(63)
theorem scenario_rows (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (has : a ∈ s) (hbs : b ∈ s)
    (hs : s ⊆ Ici a ∪ Ici b) : ∀ e ∈ Examples.all, ∀ i ∈ wh? e, ∀ v ∈ e.verdict,
      (IsExhaustivelyResolvable (box (i.1.hamblinSet i.2) permits) s ↔ v = true) := by
  simp only [Range.freeChoice_iff ha hb hab has hbs hs]
  decide +kernel

example : Datum.ChecksVerdict wh? (fun i ↦ decide (i.1 = .quantifiers ∧ i.2 ≠ .plural))
    Examples.all 4 := by decide +kernel

-- the scenario (59) is satisfiable: buying either thing alone is permitted
example := scenario_rows (E := Set (Fin 2)) (a := {0}) (b := {1}) (s := {{0}, {1}})
  (Set.isAtom_singleton 0) (Set.isAtom_singleton 1) (by simp) (by simp) (by simp)
  (by rintro _ (rfl | rfl) <;> simp)

/-- A row's interrogative, where the paper judges a free choice answer to a question without
*-ro*. -/
def freeChoiceAnswer? (e : Datum) : Option (Range × Marking) :=
  (wh? e).filter fun i ↦ i.1 = .quantifiers ∧ (e.readings.lookup "free choice answer").isSome

-- (30), (31)
theorem freeChoiceAnswer_rows (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (has : a ∈ s)
    (hbs : b ∈ s) (hs : s ⊆ Ici a ∪ Ici b) : ∀ e ∈ Examples.all, ∀ i ∈ freeChoiceAnswer? e,
      (IsExhaustivelyResolvable (box (i.1.hamblinSet i.2) permits) s ↔
        e.readings.lookup "free choice answer" = some .acceptable) := by
  simp only [Range.freeChoice_iff ha hb hab has hbs hs]
  decide +kernel

example : Datum.ReadCount freeChoiceAnswer? Examples.all 2 := by decide +kernel

/-- A row's marking, where it combines *baham* 'together' with a collective predicate. -/
def collective? (e : Datum) : Option Marking :=
  if "baham" ∈ e.surfaceTokens then marking? e else none

-- (56), (57), each with or without *-ro*
theorem collective_rows [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ∀ e ∈ Examples.all, ∀ m ∈ collective? e,
      ((presupposition (hamblin mixed m.domain) : Set E).Nonempty ↔ e.judgment = .acceptable) ∧
        ((presupposition (hamblinRo mixed m.domain) : Set E).Nonempty ↔
          e.judgment = .acceptable) := by
  simp only [nonempty_presupposition_hamblin_mixed_iff ha hb hab,
    nonempty_presupposition_hamblinRo_mixed_iff ha hb hab]
  decide +kernel

example : Datum.ReadCount collective? Examples.all 2 := by decide +kernel

end AlonsoOvalleMoghiseh2025b
