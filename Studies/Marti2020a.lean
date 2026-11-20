module

public import Studies.Harbour2014
public import Linglib.Semantics.Plurality.Multiplicity
public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Data.Examples.Marti2020a
public import Linglib.Data.Examples.Readers

/-!
# Martí (2020): Inclusive plurals and the theory of number

A plural noun is exclusive where it is true of sums of two or more atoms only, and inclusive where
it is true of atoms as well. In Harbour's theory of number a plural is exclusive: its bundle
carries `[−atomic]`, alone in a language with a singular and a plural and with `[−minimal]` in a
language with a dual, where it is true of sums of three or more. English, Ljubljana Slovenian and
Biak plurals are nonetheless inclusive under negation, in the restriction of a universal
quantifier, in the antecedent of a conditional and in questions.

An inclusive-only account gives the plural form the denotation of the noun phrase, with no number
feature, and derives exclusivity by competition with the singular. In a system that uses
`[±atomic]`, every number but the singular is built on `[−atomic]`
(`label_eq_singular_of_notMem`), so a language whose bundles all lack `[−atomic]` has no dual and
no paucal, as Slovenian and Biak do. Withholding `[−atomic]` from the plural alone gives bundles
that no parameter setting generates (`bundles_ne_singular_dual_general`), and a theory that admits
them admits a singular and a dual without a plural, against the implications the settings derive
(`requires_dual_plural`).

Two accounts keep the typology. On the ambiguity account the plural form spells out the bundle of
the exclusive plural or a noun phrase without number, the structure of general number, and the
strongest of the two sentences is chosen (`isLeast_indef_of_monotone`,
`isLeast_indef_of_antitone`), which the judged readings of the English and Slovenian examples
bear out (`reading_isLeast`). On the account with Mayr's predicate-level exhaustivity operator the
operator does the work of `[−atomic]`: applied to the noun phrase against the singular it yields
the non-atoms (`exh_alternatives`), `[+minimal]` then yields the dual (`atomize_exh_alternatives`)
and `[−minimal]` the plural of a language with a dual (`nonMinimalOf_exh_alternatives`). Applied
above `[+minimal]` it leaves the atoms, where `[−atomic]` leaves nothing (`exh_atomize`,
`not_nonAtomsOf_atomize`).

## Implementation notes

The exhaustivity operators are `Exhaustification.exh`, at the type of individuals for the
predicate-level one and at the type of worlds for the propositional one. A sentence is the
existential closure `indef` of a region of individuals under an arbitrary verb extension, which
stands for the distributivity operator and the trace of the moved noun phrase; no maximality of
the witness is imposed. The noun phrase is an arbitrary predicate on a partial order, and the
results that compare `[+minimal]` with `[+atomic]` assume that each of its members has an atomic
part in it, as in a lattice of atoms and their sums. Number is entailed, not presupposed, as in
the paper. The settings also generate the cells one, two and three or more from a recursive
`[±minimal]` without `[±atomic]`, labelled minimal, unit augmented and augmented; the paper's
argument concerns the dual built on `[−atomic]`. Loss of a feature is the erasure of its values
from every bundle of a setting. For the examples a world is the number of witnesses, and the
sentence of a number value holds from the least cardinality of the value up, as existential
closure over sums gives (`mem_indef_subset_iff`); the negated dual is then false of three
witnesses.

## TODO

* The Biak and Bayso examples are not in the data file; Biak has no entry in the language table.
* The paper's cases of an inclusive plural in an upward-entailing environment, where the speaker
  does not know or need not say how many, are not formalized: the Strongest Meaning Hypothesis is
  applied without a context.

## References

* [marti-2020a]
* [harbour-2014]
* [mayr-2015]
* [farkas-de-swart-2010]
* [dalrymple-et-al-1998]
* [sauerland-2003]
* [spector-2007b]
-/

@[expose] public section

namespace Marti2020a

open Exhaustification Mereology Number Harbour2014

/-! ### The predicate-level exhaustivity operator -/

section Predicate

variable {D : Type*} [PartialOrder D] {P : D → Prop}

/-- The alternatives of a plural noun phrase are its own denotation and that of the singular, its
atoms. -/
def alternatives (P : D → Prop) : Set (Set D) := {{x | P x}, {x | atomsOf P x}}

/-- Exhaustified against the singular, a noun phrase is true of its non-atoms, as `[−atomic]`
makes it. -/
theorem exh_alternatives (h : ∃ x, nonAtomsOf P x) :
    exh (alternatives P) {x | P x} = {x | nonAtomsOf P x} := by
  obtain ⟨y, hy⟩ := h
  have hne : ¬ ({x | P x} : Set D) ⊆ {x | atomsOf P x} := fun hs ↦
    hy.2 (hs hy.1 : atomsOf P y).2
  rw [alternatives, exh_insert_of_subset subset_rfl, exh_singleton_of_not_subset hne]
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, atomsOf, nonAtomsOf]
  tauto

-- (77)
theorem atomize_exh_alternatives (h : ∃ x, nonAtomsOf P x) :
    atomize (· ∈ exh (alternatives P) {x | P x}) = dualOf P := by
  rw [exh_alternatives h]
  rfl

-- (76)
theorem nonMinimalOf_exh_alternatives (h : ∃ x, nonAtomsOf P x) :
    nonMinimalOf (· ∈ exh (alternatives P) {x | P x}) =
      Bundle.exact {(.atomic, false), (.minimal, false)} P := by
  rw [exh_alternatives h]
  simp only [Bundle.exact, Bundle.step, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    reduceCtorEq, Bool.true_eq_false, and_self, and_false, or_self, or_false, or_true,
    ↓reduceIte, and_true]
  rfl

theorem atomize_eq_atomsOf (hP : ∀ x, P x → ∃ a, atomsOf P a ∧ a ≤ x) :
    atomize P = atomsOf P := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h.1, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨a, ha, hax⟩ := hP x h.1
    exact (hax.antisymm (h.2 ha.1 hax)) ▸ ha
  · obtain ⟨a, ha, hay⟩ := hP y hy
    exact (h.2.2 ha.2.1 (hay.trans hyx)).trans hay

-- (80): above `[+minimal]` the operator leaves the atoms, the denotation of the singular
theorem exh_atomize (hP : ∀ x, P x → ∃ a, atomsOf P a ∧ a ≤ x) :
    exh (alternatives P) {x | atomize P x} = {x | atomsOf P x} := by
  rw [atomize_eq_atomsOf hP]
  refine exh_eq_self ?_
  rintro _ (rfl | rfl)
  exacts [fun _ h ↦ h.1, subset_rfl]

-- (80) with `[−atomic]` for the operator
theorem not_nonAtomsOf_atomize (hP : ∀ x, P x → ∃ a, atomsOf P a ∧ a ≤ x) (x : D) :
    ¬ nonAtomsOf (atomize P) x := by
  rw [atomize_eq_atomsOf hP]
  exact fun h ↦ h.2 h.1.2

end Predicate

/-! ### Sentences -/

section Sentence

variable {D W W' : Type*} {P R : D → Prop} (V : W → D → Prop)

/-- The sentence that something in the region `R` satisfies the verb. -/
def indef (R : D → Prop) : Set W := {w | ∃ x, R x ∧ V w x}

theorem indef_mono {R S : D → Prop} (h : ∀ x, R x → S x) : indef V R ⊆ indef V S :=
  fun _ ⟨x, hx, hv⟩ ↦ ⟨x, h x hx, hv⟩

/-- In an upward-entailing environment the sentence with the narrower region is the stronger,
so the exclusive plural is chosen. -/
theorem isLeast_indef_of_monotone {f : Set W → Set W'} (hf : Monotone f)
    (hR : ∀ x, R x → P x) : IsLeast {f (indef V P), f (indef V R)} (f (indef V R)) :=
  ⟨Set.mem_insert_of_mem _ rfl, by
    rintro _ (rfl | rfl)
    exacts [hf (indef_mono V hR), le_rfl]⟩

-- (56), (71), (75): downward, the sentence with the whole noun phrase is the stronger
theorem isLeast_indef_of_antitone {f : Set W → Set W'} (hf : Antitone f)
    (hR : ∀ x, R x → P x) : IsLeast {f (indef V P), f (indef V R)} (f (indef V P)) :=
  ⟨Set.mem_insert _ _, by
    rintro _ (rfl | rfl)
    exacts [le_rfl, hf (indef_mono V hR)]⟩

variable [PartialOrder D]

-- (72): the propositional operator has no alternative to deny
theorem exh_indef (hV : ∀ w x, P x → V w x → ∃ a, atomsOf P a ∧ V w a) :
    exh {indef V P, indef V (atomsOf P)} (indef V P) = indef V P :=
  exh_eq_self <| by
    rintro _ (rfl | rfl)
    exacts [subset_rfl, fun w ⟨x, hx, hv⟩ ↦ hV w x hx hv]

-- (71)
theorem exh_compl_indef :
    exh {(indef V P)ᶜ, (indef V (atomsOf P))ᶜ} (indef V P)ᶜ = (indef V P)ᶜ :=
  exh_eq_self <| by
    rintro _ (rfl | rfl)
    exacts [subset_rfl, Set.compl_subset_compl.2 (indef_mono V fun _ h ↦ h.1)]

-- witnesses of a region of sums of `k` atoms, for `k` in `S`, exist among `H` exactly when `H`
-- has at least as many atoms as some such `k`
theorem mem_indef_subset_iff {α : Type*} (S : ℕ → Prop) (H : Finset α) :
    H ∈ indef (fun H x : Finset α ↦ x ⊆ H) (fun x ↦ S x.card) ↔ ∃ k ≤ H.card, S k :=
  ⟨fun ⟨x, hx, hxH⟩ ↦ ⟨x.card, Finset.card_le_card hxH, hx⟩, fun ⟨_, hk, hS⟩ ↦
    let ⟨t, ht, e⟩ := Finset.exists_subset_card_eq hk
    ⟨t, show S t.card from e.symm ▸ hS, ht⟩⟩

end Sentence

/-! ### The typology -/

/-- In a system that uses `[±atomic]`, a bundle without `[−atomic]` is the singular. -/
theorem label_eq_singular_of_notMem :
    ∀ σ : Setting, σ.atomic ≠ .inactive → ∀ c : Convention, ∀ b ∈ σ.bundles,
      (Feature.atomic, false) ∉ b → Bundle.label c b = .singular := by
  decide

-- (50): singular, dual and a plural without number
theorem bundles_ne_singular_dual_general :
    ∀ σ : Setting, σ.bundles.toFinset ≠
      {{(.minimal, true), (.atomic, true)}, {(.minimal, true), (.atomic, false)}, ∅} := by
  decide

-- the settings derive that a dual requires a plural
theorem requires_dual_plural : Requires .dual .plural :=
  le_trans (requires_of_mem_derivedImplications (.dual, .singular) (by decide))
    (requires_of_mem_derivedImplications (.singular, .plural) (by decide))

theorem not_satisfiesUniversals_singular_dual : ¬ SatisfiesUniversals {.singular, .dual} := by
  decide

theorem not_satisfiesUniversals_singular : ¬ SatisfiesUniversals {.singular} := by decide

-- (52): the loss of `[±minimal]`
theorem bundles_erase_minimal :
    ((⟨.active, .active, .inactive⟩ : Setting).bundles.map
        (·.filter (·.1 ≠ .minimal))).toFinset =
      (⟨.active, .inactive, .inactive⟩ : Setting).bundles.toFinset := by
  decide

-- (53): the loss of `[±atomic]`
theorem bundles_erase_atomic :
    ((⟨.active, .active, .inactive⟩ : Setting).bundles.map
        (·.filter (·.1 ≠ .atomic))).toFinset =
      (⟨.inactive, .active, .inactive⟩ : Setting).bundles.toFinset := by
  decide

/-! ### The examples

A sentence with a noun of some number says that there are at least as many witnesses as some
cardinality of that number. A plural form has the inclusive and the exclusive reading, a dual form
the reading of the dual, and a form syncretic between the two has all three; the Strongest Meaning
Hypothesis selects the reading whose sentence entails the others. -/

/-- The parameter setting of each language: `[±atomic]` for English, with `[±minimal]` for
Ljubljana Slovenian. -/
def setting (e : Datum) : Option Setting :=
  e.byLanguage [(.english, ⟨.active, .inactive, .inactive⟩),
    (.slovenian, ⟨.active, .active, .inactive⟩)]

variable (s : Finset Number) {n : ℕ}

/-- The sentence that there are witnesses of a number value: at least as many as some cardinality
the system gives the value. -/
def sentence (v : Number) : Set ℕ := {n | ∃ k ≤ n, k ∈ exclusive s v}

/-- The sentence a reading gives. -/
def Examples.Reading.toSet : Examples.Reading → Set ℕ
  | .inclusive => Number.inclusive
  | .exclusive => sentence s .plural
  | .negatedDual => sentence s .dual

/-- The readings of a form. -/
def Examples.Form.readings : Examples.Form → Finset Examples.Reading
  | .plural => {.inclusive, .exclusive}
  | .dual => {.negatedDual}
  | .dualOrPlural => {.inclusive, .exclusive, .negatedDual}

/-- An environment acts on a sentence as the identity where it is upward-entailing and as
negation elsewhere. -/
def Examples.Environment.op : Examples.Environment → Set ℕ → Set ℕ
  | .upward => id
  | _ => compl

/-- The number system the setting of English generates. -/
abbrev englishSystem : Finset Number :=
  (⟨.active, .inactive, .inactive⟩ : Setting).toSystem .none

/-- The number system the setting of Ljubljana Slovenian generates. -/
abbrev slovenianSystem : Finset Number :=
  (⟨.active, .active, .inactive⟩ : Setting).toSystem .none

theorem englishSystem_eq : englishSystem = {.singular, .plural} := by decide +kernel

theorem slovenianSystem_eq : slovenianSystem = {.singular, .dual, .plural} := by decide +kernel

theorem mem_exclusive_plural_iff_two_le : n ∈ exclusive englishSystem .plural ↔ 2 ≤ n := by
  rw [englishSystem_eq]
  simp only [mem_exclusive_plural_iff, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, exactCard, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq,
    false_imp_iff, implies_true, and_true, PNat.val_ofNat]
  omega

theorem mem_exclusive_plural_iff_three_le : n ∈ exclusive slovenianSystem .plural ↔ 3 ≤ n := by
  rw [slovenianSystem_eq]
  simp only [mem_exclusive_plural_iff, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, exactCard, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq,
    false_imp_iff, implies_true, and_true, PNat.val_ofNat]
  omega

theorem sentence_plural_english : sentence englishSystem .plural = Set.Ici 2 := by
  ext n
  simp only [sentence, Set.mem_ofPred_eq, mem_exclusive_plural_iff_two_le, Set.mem_Ici]
  exact ⟨fun ⟨k, hk, h⟩ ↦ h.trans hk, fun h ↦ ⟨n, le_rfl, h⟩⟩

theorem sentence_plural_slovenian : sentence slovenianSystem .plural = Set.Ici 3 := by
  ext n
  simp only [sentence, Set.mem_ofPred_eq, mem_exclusive_plural_iff_three_le, Set.mem_Ici]
  exact ⟨fun ⟨k, hk, h⟩ ↦ h.trans hk, fun h ↦ ⟨n, le_rfl, h⟩⟩

theorem sentence_dual_slovenian : sentence slovenianSystem .dual = Set.Ici 2 := by
  ext n
  rw [slovenianSystem_eq]
  simp [sentence, exclusive, ofCard_eq_iff (v := .dual) (by decide), exactCard, eq_comm]

-- the cardinality from which the sentence of a reading holds
private def bound (σ : Setting) : Examples.Reading → ℕ
  | .inclusive => 1
  | .negatedDual => 2
  | .exclusive => if σ.minimal = .inactive then 2 else 3

private theorem inclusive_eq_Ici : inclusive = Set.Ici 1 := Set.ext fun _ ↦ mem_inclusive

private theorem toSet_slovenian (r : Examples.Reading) :
    r.toSet slovenianSystem = Set.Ici (bound ⟨.active, .active, .inactive⟩ r) := by
  cases r
  exacts [inclusive_eq_Ici, sentence_plural_slovenian, sentence_dual_slovenian]

private theorem toSet_english {r : Examples.Reading} (hr : r ≠ .negatedDual) :
    r.toSet englishSystem = Set.Ici (bound ⟨.active, .inactive, .inactive⟩ r) := by
  cases r
  exacts [inclusive_eq_Ici, sentence_plural_english, absurd rfl hr]

-- the reading `r` of a form is the strongest in the environment
private def Selects (σ : Setting) (f : Examples.Form) (env : Examples.Environment)
    (r : Examples.Reading) : Prop :=
  (∃ i ∈ f.readings, bound σ i = bound σ r) ∧
    ∀ j ∈ f.readings, if env = .upward then bound σ j ≤ bound σ r else bound σ r ≤ bound σ j

private instance (σ f env r) : Decidable (Selects σ f env r) := by unfold Selects; infer_instance

private theorem isLeast_Ici_iff {ι : Type*} (b : ι → ℕ) (S : Finset ι) (r : ι) :
    IsLeast ((fun i ↦ Set.Ici (b i)) '' S) (Set.Ici (b r)) ↔
      (∃ i ∈ S, b i = b r) ∧ ∀ j ∈ S, b j ≤ b r := by
  refine and_congr ⟨fun ⟨i, hi, h⟩ ↦ ⟨i, hi, Set.Ici_injective h⟩,
    fun ⟨i, hi, h⟩ ↦ ⟨i, hi, congrArg _ h⟩⟩ ⟨fun h j hj ↦ Set.Ici_subset_Ici.1 (h ⟨j, hj, rfl⟩), ?_⟩
  rintro h _ ⟨j, hj, rfl⟩
  exact Set.Ici_subset_Ici.2 (h j hj)

private theorem isLeast_compl_Ici_iff {ι : Type*} (b : ι → ℕ) (S : Finset ι) (r : ι) :
    IsLeast ((fun i ↦ (Set.Ici (b i))ᶜ) '' S) (Set.Ici (b r))ᶜ ↔
      (∃ i ∈ S, b i = b r) ∧ ∀ j ∈ S, b r ≤ b j := by
  refine and_congr ⟨fun ⟨i, hi, h⟩ ↦ ⟨i, hi, Set.Ici_injective (compl_injective h)⟩,
    fun ⟨i, hi, h⟩ ↦ ⟨i, hi, congrArg _ (congrArg _ h)⟩⟩
    ⟨fun h j hj ↦ Set.Ici_subset_Ici.1 (Set.compl_subset_compl.1 (h ⟨j, hj, rfl⟩)), ?_⟩
  rintro h _ ⟨j, hj, rfl⟩
  exact Set.compl_subset_compl.2 (Set.Ici_subset_Ici.2 (h j hj))

private theorem isLeast_iff_selects_of_eq {σ : Setting} {f : Examples.Form}
    (h : ∀ i ∈ f.readings, i.toSet s = Set.Ici (bound σ i)) (env : Examples.Environment)
    {r : Examples.Reading} (hr : r.toSet s = Set.Ici (bound σ r)) :
    IsLeast ((fun i : Examples.Reading ↦ env.op (i.toSet s)) '' f.readings)
        (env.op (r.toSet s)) ↔
      Selects σ f env r := by
  have himg (g : Set ℕ → Set ℕ) :
      (fun i : Examples.Reading ↦ g (i.toSet s)) '' (f.readings : Set Examples.Reading) =
        (fun i ↦ g (Set.Ici (bound σ i))) '' f.readings :=
    Set.image_congr fun i hi ↦ by rw [h i hi]
  unfold Selects
  cases env
  · rw [Examples.Environment.op, himg, hr]
    simpa [forall_and] using isLeast_Ici_iff (bound σ) f.readings r
  all_goals
    show IsLeast ((fun i : Examples.Reading ↦ (i.toSet s)ᶜ) '' _) (r.toSet s)ᶜ ↔ _
    rw [himg compl, hr]
    simpa [forall_and] using isLeast_compl_Ici_iff (bound σ) f.readings r

private theorem selects_of_mem :
    ∀ e ∈ Examples.all, ∀ σ ∈ setting e, ∀ f ∈ Examples.form e, ∀ env ∈ Examples.environment e,
      ∀ r, (σ = ⟨.active, .active, .inactive⟩ ∨
          (σ = ⟨.active, .inactive, .inactive⟩ ∧ f = .plural ∧
            ((Examples.reading e r).isSome → r ≠ .negatedDual))) ∧
        (Examples.reading e r = some .acceptable → Selects σ f env r) ∧
        (Examples.reading e r = some .unacceptable → ¬ Selects σ f env r) := by
  decide

/-- A reading the paper accepts is the one the Strongest Meaning Hypothesis selects among the
readings of the form, and a reading it rejects is not. -/
theorem reading_isLeast :
    ∀ e ∈ Examples.all, ∀ σ ∈ setting e, ∀ f ∈ Examples.form e, ∀ env ∈ Examples.environment e,
      ∀ r,
        (Examples.reading e r = some .acceptable →
          IsLeast ((fun i : Examples.Reading ↦ env.op (i.toSet (σ.toSystem .none))) '' f.readings)
            (env.op (r.toSet (σ.toSystem .none)))) ∧
        (Examples.reading e r = some .unacceptable →
          ¬ IsLeast ((fun i : Examples.Reading ↦ env.op (i.toSet (σ.toSystem .none))) '' f.readings)
            (env.op (r.toSet (σ.toSystem .none)))) := by
  intro e he σ hσ f hf env henv r
  obtain ⟨hcase, hacc, hunacc⟩ := selects_of_mem e he σ hσ f hf env henv r
  have key : (Examples.reading e r).isSome →
      (IsLeast ((fun i : Examples.Reading ↦ env.op (i.toSet (σ.toSystem .none))) '' f.readings)
        (env.op (r.toSet (σ.toSystem .none))) ↔ Selects σ f env r) := by
    intro hsome
    rcases hcase with rfl | ⟨rfl, rfl, hnd⟩
    · exact isLeast_iff_selects_of_eq _ (fun i _ ↦ toSet_slovenian i) env (toSet_slovenian r)
    · exact isLeast_iff_selects_of_eq _
        (fun i hi ↦ toSet_english (by rintro rfl; exact absurd hi (by decide))) env
        (toSet_english (hnd hsome))
  exact ⟨fun h ↦ (key (by simp [h])).2 (hacc h), fun h hl ↦ hunacc h ((key (by simp [h])).1 hl)⟩

/-- The exclusive plural is true of as many as the paper reports: two or more in English, three
or more in Ljubljana Slovenian. -/
theorem sentence_plural_eq_Ici :
    ∀ e ∈ Examples.all, ∀ σ ∈ setting e, ∀ k ∈ e.nat? "at_least",
      sentence (σ.toSystem .none) .plural = Set.Ici k := by
  have h : ∀ e ∈ Examples.all, ∀ σ ∈ setting e, ∀ k ∈ e.nat? "at_least",
      σ = ⟨.active, .inactive, .inactive⟩ ∧ k = 2 ∨ σ = ⟨.active, .active, .inactive⟩ ∧ k = 3 := by
    decide
  intro e he σ hσ k hk
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h e he σ hσ k hk
  exacts [sentence_plural_english, sentence_plural_slovenian]

end Marti2020a
