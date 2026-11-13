module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Atoms
public import Mathlib.Data.Set.Lattice.Order
public import Linglib.Data.Examples.Dayal2016
public import Linglib.Data.Examples.Readers
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Semantics.Questions.Number

/-!
# Dayal (2016): Questions

This file formalizes the theory of questions of the second chapter of Dayal's *Questions*. A
question denotes its Hamblin set, and the answerhood operator Ans-D returns the true member that
entails every true member, if there is one. [Scope marking needs the false members
too](##trueAnswers_karttunen_composition). [Ans-D is defined exactly where the situation lies in
the domain of the *wh* phrase](##Question.isExhaustivelyResolvable_whHamblin_iff), the atoms for
singular *which N*, so [a polar question with one is
unanswerable](##not_isExhaustivelyResolvable_polarWh_singular), while [Beck and Rullmann's
intersection of the true members ignores number](##Question.weakAnswer_whHamblin) and [maximality
inside the *wh* phrase agrees with Ans-D](##mem_trueAnswers_maxHamblin_iff). The plurality of plural
*which N* is [an implicature of competition with the singular](##Question.whFelicitous_plural). The
existential presupposition is soft and that of a cleft hard, so [only another speaker can deny it
and only an ordinary question suspend it](##coherent_iff).

## Implementation notes

* A situation is identified with the plurality the nucleus holds of, so the nucleus proposition
  for `x` is `Set.Ici x`; this builds in the distributivity the chapter's entailments assume
  (*John likes Mary and Betty* entails *John likes Mary*).
* The number of a *wh* phrase is read through Sauerland's domains `Number.dom`, *who* and *what*
  carrying none, as the chapter prefers to an ambiguity between a silent singular and plural
  noun; the phrase ranges over the non-null individuals of the domain.
* The chapter treats the plurality requirement as an implicature without choosing a mechanism;
  here it is Maximize Presupposition between the singular and the plural question
  (`Presupposition.strengthen`), Sauerland's mechanism among those it cites.
* An exchange is modelled by the questioner's assumptions inside the common ground. A soft
  presupposition must hold in the former, a hard one in the latter; *if anyone* restricts the
  assumptions to the presupposition, and a reply must be consistent with the common ground.

## TODO

* Lahiri's contextual restriction in place of the truth requirement (40), Rullmann's account of
  negative islands (47), and the number effects on mention-some and pair-list answers (54)–(56).
* Chapters 3–6: the weak–strong distinction and mention-some answers, pair-list and functional
  answers, embedded and concealed questions, and weak islands through maximality.

## References

* [V. Dayal, *Questions* (2016)][dayal-2016]
* [V. Dayal, *Locality in WH quantification* (1996)][dayal-1996]
* [V. Dayal, *Scope marking as indirect wh-dependency* (1994)][dayal-1994]
* [L. Karttunen, *Syntax and semantics of questions* (1977)][karttunen-1977]
* [I. Heim, *Interrogative semantics and Karttunen's semantics for know*
  (1994)][heim-1994]
* [J. Groenendijk and M. Stokhof, *Studies on the semantics of questions*
  (1984)][groenendijk-stokhof-1984]
* [H. Rullmann, *Maximality in the semantics of wh-constructions* (1995)][rullmann-1995]
* [S. Beck and H. Rullmann, *A flexible approach to exhaustivity in questions*
  (1999)][beck-rullmann-1999]
* [M. Bittner, *Cross-linguistic semantics for questions* (1998)][bittner-1998]
* [U. Lahiri, *Questions and answers in embedded contexts* (2002)][lahiri-2002]
* [U. Sauerland, *A new semantics for number* (2003)][sauerland-2003]
* [D. Abusch, *Presupposition triggering from alternatives* (2010)][abusch-2010]
* [L. Karttunen and S. Peters, *What indirect questions conventionally
  implicate* (1976)][karttunen-peters-1976]
* [R. Sharvy, *A more general theory of definite descriptions* (1980)][sharvy-1980]
* [G. Link, *The logical analysis of plurals and mass terms* (1983)][link-1983]
* [J. Hintikka, *Knowledge and belief* (1962)][hintikka-1962]
-/

@[expose] public section

namespace Dayal2016

open Question Set
open Mereology (atom_iff_isAtom)
open Presupposition (Hardness)

/-! ### Scope marking -/

/-- Where Mary may be. -/
inductive Place
  | london
  | paris
  deriving DecidableEq

/-- A world fixes where Mary is and where John thinks she is. -/
abbrev World := Place × Place

/-- The nucleus of *Where is Mary?*: Mary is at `x`. -/
def isAt (x : Place) : Set World := {w | w.1 = x}

/-- John's doxastic alternatives: the worlds where Mary is where he thinks she is. -/
def believes : SetRel World World := {p | p.2.1 = p.1.2}

/-- *John thinks that q*: the [hintikka-1962] box over `believes`. -/
def think (q : Set World) : Set World := {w | ModalLogic.Box believes (· ∈ q) w}

/-- The Hamblin set of *Where is Mary?*. -/
def whereMary : Set (Set World) := range isAt

/-- *What does John think? Where is Mary?*: the first question quantifies over propositions with
`whereMary` as its restriction. -/
def scopeMarked : Set (Set World) := think '' whereMary

/-- Mary is in Paris and John thinks she is in London. -/
def w₀ : World := (.paris, .london)

-- (36b), (37c)
theorem trueAnswers_whereMary : trueAnswers whereMary w₀ = {isAt .paris} := by
  rw [whereMary, trueAnswers_range,
    show {x | w₀ ∈ isAt x} = {.paris} by ext x; simp [isAt, w₀, eq_comm], image_singleton]

-- (35b), (37b)
theorem trueAnswers_scopeMarked : trueAnswers scopeMarked w₀ = {think (isAt .london)} := by
  rw [scopeMarked, whereMary, ← range_comp, trueAnswers_range,
    show {x | w₀ ∈ (think ∘ isAt) x} = {.london} by
      ext x
      simp only [think, ModalLogic.Box, believes, isAt, w₀, mem_ofPred_eq, Function.comp]
      exact ⟨fun h ↦ (h (.london, .london) rfl).symm, fun h v hv ↦ hv.trans h.symm⟩,
    image_singleton]
  rfl

/-- Built on the true members of *Where is Mary?* alone, *What does John think? Where is Mary?*
has no true member, although *John thinks Mary is in London* answers it. -/
theorem trueAnswers_karttunen_composition :
    trueAnswers (think '' trueAnswers whereMary w₀) w₀ = ∅ := by
  rw [trueAnswers_whereMary, image_singleton]
  ext p
  simp only [mem_trueAnswers, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
  rintro rfl hw
  exact absurd (hw (.london, .london) rfl) (by simp [isAt])

-- (37b)
theorem dayalAns_scopeMarked : dayalAns scopeMarked w₀ = some (think (isAt .london)) := by
  rw [dayalAns_eq_some_iff, IsStrongestTrueAnswer, trueAnswers_scopeMarked]
  exact isLeast_singleton _

/-! ### Number -/

section Number

variable {E : Type*} [CompleteLattice E]

-- `Question.whDomain` is (63) and `Question.whHamblin` (44), (63); `Question.weakAnswer_whHamblin`
-- is (52) and `Question.isExhaustivelyResolvable_whHamblin_iff` (49), (50), (65), (66);
-- `Question.whFelicitous` and `Question.notMem_whFelicitous_bot` give (57a), (65), (66).

-- (51)
/-- *Does John like which woman/women?*: each member of the Hamblin set and its negation. -/
def polarWh (n : Option Number) : Set (Set E) := whHamblin n ∪ compl '' whHamblin n

theorem mem_polarWh {n : Option Number} {p : Set E} :
    p ∈ polarWh n ↔ ∃ x ∈ whDomain n, Ici x = p ∨ (Ici x)ᶜ = p := by
  rw [polarWh, whHamblin, image_image]
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    exacts [⟨x, hx, Or.inl h⟩, ⟨x, hx, Or.inr h⟩]
  · rintro ⟨x, hx, h | h⟩
    exacts [Or.inl ⟨x, hx, h⟩, Or.inr ⟨x, hx, h⟩]

private theorem eq_of_Ici_eq_singleton {x w y : E} (h : Ici x = {w}) (hy : x ≤ y) : y = x :=
  (h.symm ▸ hy : y ∈ ({w} : Set E)).trans (h.symm ▸ le_rfl : x ∈ ({w} : Set E)).symm

private theorem le_of_compl_Ici_eq_singleton {x w c : E} (hx : x ≠ ⊥) (h : (Ici x)ᶜ = {w})
    (hc : c ≠ ⊥) : x ≤ c :=
  not_not.1 fun hxc ↦ hc <| (h.symm ▸ hxc : c ∈ ({w} : Set E)).trans
    (h.symm ▸ fun h0 ↦ hx (le_bot_iff.1 h0) : ⊥ ∈ ({w} : Set E)).symm

/-! ### Ans-D on the number paradigm -/

variable [IsAtomistic E]

-- (49c), (50c), (65b), (66b)
theorem dayalAns_hamblin {n : Option Number} {w : E} (h : w ∈ whDomain n) :
    dayalAns (whHamblin n) w = some (Ici w) :=
  (dayalAns_eq_some_iff _ _).2 <|
    (isStrongestTrueAnswer_iff _ _).2 ⟨⟨w, h, rfl⟩, (weakAnswer_whHamblin n w).symm⟩

theorem strongAnswer_hamblin (n : Option Number) (w : E) :
    strongAnswer (whHamblin n) w = {w} := by
  ext v
  simp only [mem_strongAnswer, whHamblin, forall_mem_image, mem_Ici, mem_singleton_iff]
  constructor
  · intro h
    have key : {x ∈ whDomain n | x ≤ w} = {x ∈ whDomain n | x ≤ v} :=
      ext fun _ => and_congr_right fun hx => h hx
    rw [← sSup_whDomain_le n w, key, sSup_whDomain_le n v]
  · rintro rfl
    exact fun _ _ => Iff.rfl

-- (65c), (66c)
theorem dayalStrongAns_hamblin {n : Option Number} {w : E} (h : w ∈ whDomain n) :
    dayalStrongAns (whHamblin n) w = some {w} :=
  (dayalStrongAns_eq_some_iff _ _).2
    ⟨(isExhaustivelyResolvable_whHamblin_iff n w).2 h, (strongAnswer_hamblin n w).symm⟩

-- (46)
/-- Maximality in the *wh* phrase: the member for `x` says that `x` is the maximal individual John
likes, true in the situation `x` alone. -/
def maxHamblin (n : Option Number) : Set (Set E) := (fun x ↦ {x}) '' whDomain n

-- p. 46: maximality in the wh phrase replicates Ans-D on single wh questions
theorem mem_trueAnswers_maxHamblin_iff {n : Option Number} {w : E} {p : Set E} :
    p ∈ trueAnswers (maxHamblin n) w ↔ dayalStrongAns (whHamblin n) w = some p := by
  rw [dayalStrongAns_eq_some_iff, isExhaustivelyResolvable_whHamblin_iff, strongAnswer_hamblin]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, rfl⟩

/-! ### Polar questions with a *wh* phrase -/

-- the weak answer of the polar question is the strong answer of the wh question
theorem isExhaustivelyResolvable_polarWh_iff (n : Option Number) (w : E) :
    IsExhaustivelyResolvable (polarWh n) w ↔ {w} ∈ polarWh n := by
  rw [isExhaustivelyResolvable_iff, polarWh, weakAnswer_union_image_compl, strongAnswer_hamblin]

-- (51b)
/-- With two atoms, a polar question with a singular *wh* phrase has no strongest true member in
any situation. -/
theorem not_isExhaustivelyResolvable_polarWh_singular {a b : E} (ha : IsAtom a) (hb : IsAtom b)
    (hab : a ≠ b) (w : E) : ¬ IsExhaustivelyResolvable (polarWh (some .singular)) w := by
  rw [isExhaustivelyResolvable_polarWh_iff, mem_polarWh]
  rintro ⟨x, hx, h | h⟩ <;> have hx := mem_whDomain_singular.1 hx
  · have key : ∀ {c : E}, IsAtom c → c = x := fun {c} hc ↦ (hx.le_iff_eq hc.ne_bot).1
      (eq_of_Ici_eq_singleton h (le_sup_right : x ≤ c ⊔ x) ▸ (le_sup_left : c ≤ c ⊔ x))
    exact hab ((key ha).trans (key hb).symm)
  · have key : ∀ {c : E}, IsAtom c → x = c := fun {c} hc ↦
      (hc.le_iff_eq hx.ne_bot).1 (le_of_compl_Ici_eq_singleton hx.ne_bot h hc.ne_bot)
    exact hab ((key ha).symm.trans (key hb))

-- (51c)
theorem isExhaustivelyResolvable_polarWh_plural_iff {a b : E} (ha : IsAtom a) (hb : IsAtom b)
    (hab : a ≠ b) (w : E) : IsExhaustivelyResolvable (polarWh (some .plural)) w ↔ w = ⊤ := by
  rw [isExhaustivelyResolvable_polarWh_iff, mem_polarWh]
  constructor
  · rintro ⟨x, hx, h | h⟩
    · exact (h.symm ▸ le_top : (⊤ : E) ∈ ({w} : Set E)).symm
    · have hx := mem_whDomain_plural.1 hx
      have key : ∀ {c : E}, IsAtom c → x = c := fun {c} hc ↦
        (hc.le_iff_eq hx).1 (le_of_compl_Ici_eq_singleton hx h hc.ne_bot)
      exact absurd ((key ha).symm.trans (key hb)) hab
  · rintro rfl
    exact ⟨⊤, mem_whDomain_plural.2 fun h ↦ ha.ne_bot (le_bot_iff.1 (h ▸ le_top)), .inl Ici_top⟩

end Number

/-! ### Soft and hard existential presuppositions -/

section Existence

variable {W : Type*} (P : Set W)

-- (60)
/-- Where a question's existential presupposition `P` must hold, given the questioner's
assumptions `σ` and the common ground `c`: in `σ` for a soft trigger, the ordinary question, and
in `c` for a hard one, the cleft. -/
def Presupposed : Hardness → Set W → Set W → Prop
  | .soft, σ, _ => σ ⊆ P
  | .hard, _, c => c ⊆ P

/-- How the nonexistence of a witness enters an exchange. -/
inductive Nonexistence
  /-- The questioner doubts or denies that there is one. -/
  | questioner
  /-- The questioner suspends the presupposition with *if anyone*. -/
  | suspended
  /-- The other participant denies that there is one. -/
  | other
  deriving DecidableEq

/-- An exchange is coherent when some assumptions of the questioner, inside the common ground,
satisfy the presupposition and leave nonexistence open where the exchange puts it. -/
def Coherent (h : Hardness) : Nonexistence → Prop
  | .questioner => ∃ σ c, σ ⊆ c ∧ Presupposed P h σ c ∧ (σ \ P).Nonempty
  | .suspended => ∃ σ c, σ ⊆ c ∧ Presupposed P h (σ ∩ P) c ∧ (σ \ P).Nonempty
  | .other => ∃ σ c, σ.Nonempty ∧ σ ⊆ c ∧ Presupposed P h σ c ∧ (c \ P).Nonempty

/-- A contingent existential presupposition can be suspended by the questioner or denied by the
other participant exactly when it is soft, and the questioner can never simply doubt it. -/
theorem coherent_iff {P : Set W} (hP : P.Nonempty) (hP' : Pᶜ.Nonempty) {h : Hardness}
    {x : Nonexistence} : Coherent P h x ↔ h = .soft ∧ x ≠ .questioner := by
  obtain ⟨v, hv⟩ := hP'
  cases h <;> cases x <;> simp only [Coherent, Presupposed, ne_eq, reduceCtorEq, and_false,
    and_true, not_true_eq_false, not_false_eq_true, iff_false, iff_true, not_exists, not_and]
  · exact fun σ c hσc hc ⟨w, hw, hwP⟩ ↦ hwP (hc (hσc hw))
  · exact fun σ c hσc hc ⟨w, hw, hwP⟩ ↦ hwP (hc (hσc hw))
  · exact fun σ c _ _ hc ⟨w, hw, hwP⟩ ↦ hwP (hc hw)
  · exact fun σ c _ hσ ⟨w, hw, hwP⟩ ↦ hwP (hσ hw)
  · exact ⟨univ, univ, subset_rfl, inter_subset_right, v, trivial, hv⟩
  · exact ⟨P, univ, hP, subset_univ _, subset_rfl, v, trivial, hv⟩

end Existence

/-! ### Scales -/

-- (53a), (53b)
theorem isStrongestTrueAnswer_range_Iic {α : Type*} [Preorder α] (t : α) :
    IsStrongestTrueAnswer (range (Iic : α → Set α)) t (Iic t) :=
  isStrongestTrueAnswer_range_iff.2 ⟨le_rfl, fun _ ↦ Iic_subset_Iic.2⟩

-- (53c), (53d)
theorem isStrongestTrueAnswer_range_Ici {α : Type*} [Preorder α] (c : α) :
    IsStrongestTrueAnswer (range (Ici : α → Set α)) c (Ici c) :=
  isStrongestTrueAnswer_range_iff.2 ⟨le_rfl, fun _ ↦ Ici_subset_Ici.2⟩

/-! ### The chapter's women -/

/-- The women of (44). -/
inductive Woman
  | mary
  | sue
  | betty
  deriving DecidableEq, Fintype

open Woman

private theorem not_isAtom_pair {x y : Woman} (h : x ≠ y) : ¬ IsAtom ({x, y} : Set Woman) := by
  rw [insert_eq, ← atom_iff_isAtom]
  exact Mereology.not_atom_sup_of_ne (atom_iff_isAtom.2 (isAtom_singleton x))
    (atom_iff_isAtom.2 (isAtom_singleton y)) (by simpa using h)

private theorem mary_ne_sue : ({mary} : Set Woman) ≠ {sue} :=
  fun h => (by decide : mary ≠ sue) (singleton_eq_singleton_iff.1 h)

-- (49)
example : dayalAns (whHamblin (some .singular)) ({mary} : Set Woman) = some (Ici {mary}) :=
  dayalAns_hamblin (mem_whDomain_singular.2 (isAtom_singleton mary))

-- (49)
example : ¬ IsExhaustivelyResolvable (whHamblin (some .singular)) ({mary, sue} : Set Woman) :=
  fun h => not_isAtom_pair (by decide)
    (mem_whDomain_singular.1 ((isExhaustivelyResolvable_whHamblin_iff _ _).1 h))

-- (50)
example : dayalAns (whHamblin (some .plural)) ({mary, betty} : Set Woman) =
    some (Ici {mary, betty}) :=
  dayalAns_hamblin <| mem_whDomain_plural.2 (insert_nonempty _ _).ne_empty

-- (50): Ans-D is defined, the plurality implicature fails
example : dayalAns (whHamblin (some .plural)) ({mary} : Set Woman) = some (Ici {mary}) ∧
    ({mary} : Set Woman) ∉ whFelicitous (some .plural) :=
  ⟨dayalAns_hamblin <| mem_whDomain_plural.2 (singleton_ne_empty _),
   fun h => ((whFelicitous_plural (isAtom_singleton mary) (isAtom_singleton sue) mary_ne_sue).symm ▸
     h).2 (isAtom_singleton _)⟩

-- (51)
example : (∀ w : Set Woman, ¬ IsExhaustivelyResolvable (polarWh (some .singular)) w) ∧
    ∀ w : Set Woman, IsExhaustivelyResolvable (polarWh (some .plural)) w ↔ w = univ :=
  ⟨not_isExhaustivelyResolvable_polarWh_singular (isAtom_singleton mary) (isAtom_singleton sue)
    mary_ne_sue,
   isExhaustivelyResolvable_polarWh_plural_iff (isAtom_singleton mary) (isAtom_singleton sue)
    mary_ne_sue⟩

-- (52): Beck and Rullmann's answer to the singular question when John likes Mary and Sue
example : weakAnswer (whHamblin (some .singular)) ({mary, sue} : Set Woman) = Ici {mary, sue} ∧
    Ici ({mary, sue} : Set Woman) ∉ whHamblin (some .singular) :=
  ⟨weakAnswer_whHamblin _ _,
   fun ⟨_, hx, h⟩ => not_isAtom_pair (by decide) (Ici_injective h ▸ mem_whDomain_singular.1 hx)⟩

/-! ### The chapter's judgments -/

theorem isAtom_coe_iff (s : Finset Woman) : IsAtom (s : Set Woman) ↔ s.card = 1 := by
  rw [Set.isAtom_iff, Finset.card_eq_one]
  exact exists_congr fun _ => Finset.coe_eq_singleton

theorem coe_mem_felicitous_iff (n : Option Number) (s : Finset Woman) :
    (s : Set Woman) ∈ whFelicitous n ↔
      (n = some .singular → s.card = 1) ∧ (n ≠ some .singular → s ≠ ∅) ∧
        (n ≠ none → n ≠ some .singular → s.card ≠ 1) := by
  rcases n with _ | m
  · simp [whFelicitous_none, Finset.coe_eq_empty]
  · by_cases hm : m = .singular
    · subst hm
      simp [whFelicitous_singular, isAtom_coe_iff]
    · rw [whFelicitous_of_ne_singular (isAtom_singleton mary) (isAtom_singleton sue) mary_ne_sue hm]
      simp [hm, Finset.coe_eq_empty, isAtom_coe_iff]

instance (n : Option Number) (s : Finset Woman) : Decidable ((s : Set Woman) ∈ whFelicitous n) :=
  decidable_of_iff _ (coe_mem_felicitous_iff n s).symm

-- (41), (42), (65), (66)
theorem rows_agree : ∀ e ∈ Examples.all,
    ∀ n ∈ e.parse? "whNumber"
      [("singular", some .singular), ("plural", some .plural), ("neutral", none)],
      ∀ s ∈ e.parse? "situation"
        ([("none", ∅), ("one", {mary}), ("two", {mary, sue})] : List (String × Finset Woman)),
        (e.judgment = .acceptable ↔ (s : Set Woman) ∈ whFelicitous n) := by
  decide

/-- How a row puts the nonexistence of a witness into the exchange. -/
def nonexistence (e : Datum) : Option Nonexistence :=
  match e.feature? "existence", e.feature? "speaker" with
  | some "suspended", _ => some .suspended
  | some _, some "other" => some .other
  | some _, some "same" => some .questioner
  | _, _ => none

-- (57)–(59), (61)
theorem existence_rows : ∀ e ∈ Examples.all,
    ∀ h ∈ e.parse? "cleft" [("true", Hardness.hard), ("false", .soft)], ∀ x ∈ nonexistence e,
      (e.judgment = .acceptable ↔
        Coherent {w : Set Woman | IsExhaustivelyResolvable (whHamblin none) w} h x) := by
  have hP : {w : Set Woman | IsExhaustivelyResolvable (whHamblin none) w}.Nonempty :=
    ⟨{mary}, (isExhaustivelyResolvable_whHamblin_iff _ _).2 ⟨trivial, singleton_ne_empty _⟩⟩
  have hP' : {w : Set Woman | IsExhaustivelyResolvable (whHamblin none) w}ᶜ.Nonempty :=
    ⟨∅, fun h => ((isExhaustivelyResolvable_whHamblin_iff _ _).1 h).2 rfl⟩
  simp only [coherent_iff hP hP']
  decide

end Dayal2016
