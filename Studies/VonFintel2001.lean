module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Data.Examples.VonFintel2001

/-!
# von Fintel (2001): Conditional Strengthening

This file formalizes [von-fintel-2001]'s account of the strengthening of conditionals beyond
their truth conditions. A conditional *if p, q* is a restricted universal over the relevant
situations (5), `Conditional.strictImp`, and the conditional perfection of [geis-zwicky-1971],
*if not p, not q*, is not entailed. The paper argues with [lilje-1972] that perfection does not
arise routinely, but a weaker strengthening does: by the quantity reasoning [gamut-1991]
formalizes as correct use (12), `CorrectUse`, the assertion of *if p, q* competes with the
stronger *q no matter what* (14), universal quantification over antecedents that reduces to
*q* throughout the relevant situations, so the speaker is taken not to believe that *q* holds
unconditionally, an implicature which, against [horn-2000], falls short of perfection. True
perfection arises by the presumption of exhaustivity of [cornulier-1983], the exclusion of
*if p or r, q* for the alternative antecedents `r`: over all alternatives not entailing `p` this
is perfection, over a narrower set only the relativized perfection of (18). What makes the
exclusion required is the exhaustive interpretation of answers of [groenendijk-stokhof-1984]:
a conditional asserted as the answer to *under which conditions does q hold?* is exhaustified
against the answers naming the alternative antecedents (`exhaustifiedAnswer`), which yields a
typology of cases without perfection, among them the yes/no conditional question, whose
answer has no alternative to exclude.

## Implementation notes

Situations are worlds and the relevant situations are given by an accessibility function.
Belief and relevance are predicates on propositions, so an implicature is what every correct
use of the sentence carries, and the step from not believing a proposition to believing its
negation is an explicit opinionatedness hypothesis. The exclusion of the alternative answers
is the innocent-exclusion operator `exhIE`, over alternatives indexed by their antecedents. The
monotonicity condition on scales of [matsumoto-1995] and the semantic exhaustivity of
Groenendijk and Stokhof are not formalized.

## References

* [von-fintel-2001]
* [geis-zwicky-1971]
* [lilje-1972]
* [gamut-1991]
* [horn-2000]
* [cornulier-1983]
* [groenendijk-stokhof-1984]
* [matsumoto-1995]
-/

@[expose] public section

namespace VonFintel2001

open Conditional Exhaustification

variable {W ι : Type*} {acc : W → Set W} {p q r : Set W} {s : W}

/-! ### Conditionals and perfection -/

/-- Perfection, *if not p, not q*, says that no relevant situation outside `p` is a
`q`-situation. -/
def perfection (acc : W → Set W) (p q : Set W) : Set W := strictImp acc pᶜ qᶜ

theorem mem_perfection : s ∈ perfection acc p q ↔ ∀ s' ∈ acc s, s' ∉ p → s' ∉ q :=
  mem_strictImp_forall

/-! ### Quantity implicatures (12), (13) -/

/-- Gamut's conditions of correct use (12) require that the speaker believes the sentence, holds
it relevant, and believes and holds relevant no strictly stronger sentence. -/
structure CorrectUse (bel rel : Set W → Prop) (A : Set W) : Prop where
  believes : bel A
  relevant : rel A
  quantity : ∀ B, B ⊂ A → ¬ (bel B ∧ rel B)

/-- `P` is an implicature of `A` when it follows from the conditions of correct use, whatever
the speaker's beliefs (13). -/
def Implicature (rel : Set W → Prop) (A : Set W) (P : (Set W → Prop) → Prop) : Prop :=
  ∀ bel, CorrectUse bel rel A → P bel

variable {bel rel : Set W → Prop} {A B : Set W}

/-- A relevant proposition strictly stronger than the assertion is implicated not to be
believed. -/
theorem implicature_not_bel (hB : B ⊂ A) (hrel : rel B) : Implicature rel A (fun bel ↦ ¬ bel B) :=
  fun _ h hb ↦ h.quantity B hB ⟨hb, hrel⟩

/-- An opinionated speaker is taken to believe the negation of the stronger proposition, the
further step of Mill's reasoning. -/
theorem bel_compl_of_correctUse (h : CorrectUse bel rel A) (hB : B ⊂ A) (hrel : rel B)
    (hop : bel B ∨ bel Bᶜ) : bel Bᶜ :=
  hop.resolve_left fun hb ↦ h.quantity B hB ⟨hb, hrel⟩

/-! ### *q* no matter what (14), (15) -/

/-- *q no matter what* says that every antecedent conditionally yields `q` (14). -/
def noMatterWhat (acc : W → Set W) (q : Set W) : Set W := ⋂ r : Set W, strictImp acc r q

/-- *q no matter what* is `q` throughout the relevant situations (15). -/
theorem mem_noMatterWhat : s ∈ noMatterWhat acc q ↔ acc s ⊆ q := by
  simp only [noMatterWhat, Set.mem_iInter, mem_strictImp]
  exact ⟨fun h ↦ by simpa using h Set.univ, fun h _ ↦ Set.inter_subset_left.trans h⟩

/-- *q no matter what* entails *if p, q*, the stronger alternative of the quantity reasoning. -/
theorem noMatterWhat_subset_strictImp : noMatterWhat acc q ⊆ strictImp acc p q :=
  Set.iInter_subset _ p

/-- Correct use of *if p, q*, with the unconditional claim relevant and strictly stronger,
implicates that the speaker does not believe *q* holds no matter what. -/
theorem implicature_not_noMatterWhat (hlt : noMatterWhat acc q ⊂ strictImp acc p q)
    (hrel : rel (noMatterWhat acc q)) :
    Implicature rel (strictImp acc p q) (fun bel ↦ ¬ bel (noMatterWhat acc q)) :=
  implicature_not_bel hlt hrel

theorem exists_not_noMatterWhat_not_perfection :
    ∃ (acc : Fin 3 → Set (Fin 3)) (p q : Set (Fin 3)) (s : Fin 3),
      s ∈ strictImp acc p q ∧ s ∉ noMatterWhat acc q ∧ s ∉ perfection acc p q :=
  ⟨fun _ ↦ Set.univ, {0}, {0, 1}, 0, by
    simp only [mem_strictImp_forall, mem_noMatterWhat, perfection, Set.mem_univ, Set.subset_def,
      Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_compl_iff, true_implies]
    decide⟩

/-! ### The road to true perfection -/

/-- *If p or r, q* is stronger than *if p, q*, by the downward monotonicity of the universal. -/
theorem strictImp_union_subset : strictImp acc (p ∪ r) q ⊆ strictImp acc p q :=
  strictImp_anti_left Set.subset_union_left

theorem exists_of_not_mem_strictImp_union (h : s ∈ strictImp acc p q)
    (h' : s ∉ strictImp acc (p ∪ r) q) : ∃ s' ∈ acc s, s' ∈ r ∧ s' ∉ q := by
  by_contra hne
  exact h' fun x ⟨hx, hpr⟩ ↦ hpr.elim (fun hp ↦ h ⟨hx, hp⟩)
    (fun hr ↦ by_contra fun hq ↦ hne ⟨x, hx, hr, hq⟩)

/-- Excluding *if r, q* for every antecedent `r` not entailing `p` is perfection (7). -/
theorem perfection_of_forall (h : ∀ r : Set W, ¬ r ⊆ p → s ∉ strictImp acc r q) :
    s ∈ perfection acc p q := by
  rw [mem_perfection]
  intro s' hs' hp hq
  exact h {s'} (fun h ↦ hp (h rfl)) fun _ ⟨_, hx⟩ ↦ Set.mem_singleton_iff.1 hx ▸ hq

/-- Relativized perfection (18), excluding the alternatives of a narrower set of antecedents,
falls short of perfection. Situation `0` is a call after midnight, `1` a polite call before
midnight and `2` an insulting one; excluding *if you call before midnight, I will be upset*
leaves the insult upsetting. -/
theorem exists_relativized_not_perfection :
    ∃ (acc : Fin 3 → Set (Fin 3)) (p q : Set (Fin 3)) (R : Set (Set (Fin 3))) (s : Fin 3),
      s ∈ strictImp acc p q ∧ (∀ r ∈ R, ¬ r ⊆ p → s ∉ strictImp acc r q) ∧
        s ∉ perfection acc p q :=
  ⟨fun _ ↦ Set.univ, {0}, {0, 2}, {{1, 2}}, 0, by
    simp only [mem_strictImp_forall, perfection, Set.mem_univ, Set.subset_def,
      Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_compl_iff, true_implies,
      forall_eq]
    decide⟩

/-! ### Exhaustive answers -/

/-- The answers competing with "antecedent `t` yields the consequent" are the answers for the
other antecedents in `triggers`. -/
def answerAlternatives (causes : ι → Set W) (triggers : Set ι) (t : ι) : Set (Set W) :=
  causes '' (triggers \ {t})

/-- The exhaustified answer is "antecedent `t` yields the consequent" with the other
antecedents' answers innocently excluded. -/
def exhaustifiedAnswer (causes : ι → Set W) (triggers : Set ι) (t : ι) : Set W :=
  exhIE (answerAlternatives causes triggers t) (causes t)

variable {causes : ι → Set W} {triggers : Set ι} {t t' : ι}

@[simp] theorem mem_answerAlternatives {q : Set W} :
    q ∈ answerAlternatives causes triggers t ↔ ∃ t' ∈ triggers, t' ≠ t ∧ causes t' = q := by
  simp [answerAlternatives, and_assoc]

theorem exhaustifiedAnswer_excludes (h_exh : s ∈ exhaustifiedAnswer causes triggers t)
    (h_ie : IsInnocentlyExcludable (answerAlternatives causes triggers t) (causes t)
      (causes t')) : s ∉ causes t' :=
  h_exh.2 _ h_ie

/-- The conditional *if p, q* asserted as the answer to *under which conditions does q hold?*
over the antecedents `R`. -/
def conditionalAnswer (acc : W → Set W) (R : Set (Set W)) (p q : Set W) : Set W :=
  exhaustifiedAnswer (fun r ↦ strictImp acc r q) R p

theorem perfection_of_conditionalAnswer {R : Set (Set W)} (h : s ∈ conditionalAnswer acc R p q)
    (hie : ∀ r ∈ R, r ≠ p → IsInnocentlyExcludable
      (answerAlternatives (fun r ↦ strictImp acc r q) R p) (strictImp acc p q) (strictImp acc r q))
    (hR : ∀ s' ∈ acc s, {s'} ∈ R) : s ∈ perfection acc p q := by
  rw [mem_perfection]
  intro s' hs' hp hq
  exact exhaustifiedAnswer_excludes h (hie _ (hR s' hs') fun e ↦ hp (e ▸ rfl))
    fun _ ⟨_, hx⟩ ↦ Set.mem_singleton_iff.1 hx ▸ hq

theorem conditionalAnswer_singleton : conditionalAnswer acc {p} p q = strictImp acc p q := by
  simp only [conditionalAnswer, exhaustifiedAnswer, answerAlternatives, Set.sdiff_self,
    Set.image_empty, exhIE_empty]

end VonFintel2001
