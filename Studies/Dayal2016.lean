module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Atoms
public import Mathlib.Data.Set.Lattice.Order
public import Linglib.Data.Examples.Dayal2016
public import Linglib.Data.Examples.Readers
public import Linglib.Logic.Modal.Defs
public import Linglib.Pragmatics.Competition
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Semantics.Questions.HamblinSet

/-!
# Dayal (2016): Questions

This file formalizes the theory of questions of the second chapter of Dayal's *Questions*. A
question denotes its Hamblin set, and the answerhood operator Ans-D returns the true member that
entails every true member, if there is one. [Scope marking needs the false members
too](##trueAnswers_karttunen_composition). [Ans-D is defined exactly where the situation lies in
the domain of the *wh* phrase](##isExhaustivelyResolvable_hamblin_iff), the atoms for singular
*which N*, so [a polar question with one is
unanswerable](##not_isExhaustivelyResolvable_polarWh_singular), while [Beck and Rullmann's
intersection of the true members ignores number](##weakAnswer_hamblin) and [maximality inside the
*wh* phrase agrees with Ans-D](##mem_trueAnswers_maxHamblin_iff). The plurality of plural *which N*
is [an implicature of competition with the singular](##felicitous_plural). The existential
presupposition is soft and that of a cleft hard, so [only another speaker can deny it and only an
ordinary question suspend it](##coherent_iff).

## Implementation notes

* A situation is identified with the plurality the nucleus holds of, so the nucleus proposition
  for `x` is `Set.Ici x`; this builds in the distributivity the chapter's entailments assume
  (*John likes Mary and Betty* entails *John likes Mary*).
* The number of a *wh* phrase is read through Sauerland's domains `Number.dom`, *who* and *what*
  carrying none, as the chapter prefers to an ambiguity between a silent singular and plural
  noun; the phrase ranges over the non-null individuals of the domain.
* The chapter treats the plurality requirement as an implicature without choosing a mechanism;
  here it is Maximize Presupposition between the singular and the plural question
  (`Competition.unblocked`), Sauerland's mechanism among those it cites.
* An exchange is modelled by the questioner's assumptions inside the common ground. A soft
  presupposition must hold in the former, a hard one in the latter; *if anyone* restricts the
  assumptions to the presupposition, and a reply must be consistent with the common ground.

## Errata

* (50b) prints `p_w = λw′ like_w′(j,x)` for the `p = λw′ like_w′(j,x)` of (49b), and the second
  line of (37b) equates `p` with the truth value `think_w(j,q)` where (34b) has
  `λw′ think_w′(j,p′)`.

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

open Question Set Competition
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

-- (63)
/-- The individuals a *wh* phrase of number `n` ranges over, the non-null ones in the domain of
`n`: the atoms for singular *which N*, and all of them for plural *which N* and for *who* and
*what*, which carry no number. -/
def domain (n : Option Number) : Set E := {x ∈ Number.dom n | x ≠ ⊥}

theorem mem_domain_singular {x : E} : x ∈ domain (some .singular) ↔ IsAtom x := by
  rw [domain, mem_sep_iff, Number.mem_dom_singular, Mereology.atom_iff_isAtom]
  exact ⟨And.left, fun h ↦ ⟨h, h.ne_bot⟩⟩

theorem domain_of_ne_singular {n : Option Number} (h : n ≠ some .singular) :
    domain n = {x : E | x ≠ ⊥} := by
  simp [domain, Number.dom_eq_univ_of_ne_singular h]

theorem mem_domain_plural {x : E} : x ∈ domain (some .plural) ↔ x ≠ ⊥ := by
  rw [domain_of_ne_singular (by simp)]
  rfl

theorem mem_domain_of_isAtom (n : Option Number) {a : E} (ha : IsAtom a) : a ∈ domain n := by
  by_cases h : n = some .singular
  · exact h ▸ mem_domain_singular.2 ha
  · rw [domain_of_ne_singular h]
    exact ha.ne_bot

-- (44), (63)
/-- The Hamblin set of *which N* or *who does John like?* for a *wh* phrase of number `n`: the
member for `x` is `Ici x`, the situations in which John likes `x`. -/
def hamblin (n : Option Number) : Set (Set E) := Ici '' domain n

-- (51)
/-- *Does John like which woman/women?*: each member of the Hamblin set and its negation. -/
def polarWh (n : Option Number) : Set (Set E) := hamblin n ∪ compl '' hamblin n

theorem mem_polarWh {n : Option Number} {p : Set E} :
    p ∈ polarWh n ↔ ∃ x ∈ domain n, Ici x = p ∨ (Ici x)ᶜ = p := by
  rw [polarWh, hamblin, image_image]
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

theorem sSup_domain_le (n : Option Number) (w : E) : sSup {x ∈ domain n | x ≤ w} = w :=
  le_antisymm (sSup_le fun _ hx ↦ hx.2) <| (sSup_atoms_le_eq w).ge.trans <|
    sSup_le_sSup fun _ ⟨ha, haw⟩ ↦ ⟨mem_domain_of_isAtom n ha, haw⟩

-- (52)
theorem weakAnswer_hamblin (n : Option Number) (w : E) : weakAnswer (hamblin n) w = Ici w := by
  rw [hamblin, weakAnswer, trueAnswers_image, sInter_image, ← Ici_sSup]
  exact congrArg Ici (sSup_domain_le n w)

-- (49), (50), (65), (66)
/-- Ans-D is defined on the Hamblin set of a *wh* phrase exactly in the situations its domain
contains. -/
theorem isExhaustivelyResolvable_hamblin_iff (n : Option Number) (w : E) :
    IsExhaustivelyResolvable (hamblin n) w ↔ w ∈ domain n := by
  rw [isExhaustivelyResolvable_iff, weakAnswer_hamblin, hamblin, Ici_injective.mem_set_image]

-- (49c), (50c), (65b), (66b)
theorem dayalAns_hamblin {n : Option Number} {w : E} (h : w ∈ domain n) :
    dayalAns (hamblin n) w = some (Ici w) :=
  (dayalAns_eq_some_iff _ _).2 <|
    (isStrongestTrueAnswer_iff _ _).2 ⟨⟨w, h, rfl⟩, (weakAnswer_hamblin n w).symm⟩

theorem strongAnswer_hamblin (n : Option Number) (w : E) :
    strongAnswer (hamblin n) w = {w} := by
  ext v
  simp only [mem_strongAnswer, hamblin, forall_mem_image, mem_Ici, mem_singleton_iff]
  constructor
  · intro h
    have key : {x ∈ domain n | x ≤ w} = {x ∈ domain n | x ≤ v} :=
      ext fun _ => and_congr_right fun hx => h hx
    rw [← sSup_domain_le n w, key, sSup_domain_le n v]
  · rintro rfl
    exact fun _ _ => Iff.rfl

-- (65c), (66c)
theorem dayalStrongAns_hamblin {n : Option Number} {w : E} (h : w ∈ domain n) :
    dayalStrongAns (hamblin n) w = some {w} :=
  (dayalStrongAns_eq_some_iff _ _).2
    ⟨(isExhaustivelyResolvable_hamblin_iff n w).2 h, (strongAnswer_hamblin n w).symm⟩

-- (46)
/-- Maximality in the *wh* phrase: the member for `x` says that `x` is the maximal individual John
likes, true in the situation `x` alone. -/
def maxHamblin (n : Option Number) : Set (Set E) := (fun x ↦ {x}) '' domain n

-- p. 46: maximality in the wh phrase replicates Ans-D on single wh questions
theorem mem_trueAnswers_maxHamblin_iff {n : Option Number} {w : E} {p : Set E} :
    p ∈ trueAnswers (maxHamblin n) w ↔ dayalStrongAns (hamblin n) w = some p := by
  rw [dayalStrongAns_eq_some_iff, isExhaustivelyResolvable_hamblin_iff, strongAnswer_hamblin]
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
  rintro ⟨x, hx, h | h⟩ <;> have hx := mem_domain_singular.1 hx
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
    · have hx := mem_domain_plural.1 hx
      have key : ∀ {c : E}, IsAtom c → x = c := fun {c} hc ↦
        (hc.le_iff_eq hx).1 (le_of_compl_Ici_eq_singleton hx h hc.ne_bot)
      exact absurd ((key ha).symm.trans (key hb)) hab
  · rintro rfl
    exact ⟨⊤, mem_domain_plural.2 fun h ↦ ha.ne_bot (le_bot_iff.1 (h ▸ le_top)), .inl Ici_top⟩

/-! ### The plurality implicature -/

/-- The competitors of a *wh* phrase: *which N* competes in number with the singular and the
plural, and *who* and *what*, which carry no number, with nothing. -/
def numberAlts : Option Number → Set (Option Number)
  | none => ∅
  | some _ => {some .singular, some .plural}

/-- The situations in which a *wh* question is felicitous: its existential presupposition holds
and that of no competitor with a stronger one does. -/
def felicitous (n : Option Number) : Set E :=
  unblocked numberAlts (fun m ↦ {w | IsExhaustivelyResolvable (hamblin m) w}) n

theorem felicitous_eq_unblocked_domain (n : Option Number) :
    felicitous (E := E) n = unblocked numberAlts domain n := by
  rw [felicitous]
  congr
  exact funext fun m ↦ ext (isExhaustivelyResolvable_hamblin_iff m)

theorem felicitous_none : felicitous (E := E) none = {w | w ≠ ⊥} := by
  rw [felicitous_eq_unblocked_domain, unblocked_eq_self, domain_of_ne_singular (by simp)]
  rintro ⟨_, h, -⟩
  exact h

theorem felicitous_singular : felicitous (E := E) (some .singular) = {w | IsAtom w} := by
  rw [felicitous_eq_unblocked_domain, unblocked_eq_self]
  · exact ext fun _ ↦ mem_domain_singular
  · rintro ⟨_, h | h, hss⟩ <;> rw [h] at hss
    · exact hss.ne rfl
    · exact hss.not_subset fun x hx ↦ mem_domain_of_isAtom _ (mem_domain_singular.1 hx)

theorem felicitous_of_ne_singular {a b : E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    {m : Number} (hm : m ≠ .singular) : felicitous (some m) = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  have hne : ∀ {m : Number}, m ≠ .singular → domain (some m) = {x : E | x ≠ ⊥} :=
    fun hm ↦ domain_of_ne_singular (by simpa using hm)
  have hss : domain (some .singular) ⊂ domain (E := E) (some m) := by
    refine ⟨fun x hx ↦ mem_domain_of_isAtom _ (mem_domain_singular.1 hx), fun h ↦ ?_⟩
    have hab' : a ⊔ b ∈ domain (some m) := by
      rw [hne hm]
      exact fun h0 ↦ ha.ne_bot (le_bot_iff.1 (h0 ▸ le_sup_left))
    exact Mereology.not_atom_sup_of_ne (atom_iff_isAtom.2 ha) (atom_iff_isAtom.2 hb) hab <|
      atom_iff_isAtom.2 (mem_domain_singular.1 (h hab'))
  rw [felicitous_eq_unblocked_domain,
    unblocked_eq_sdiff (alts := numberAlts) (ψ := some .singular) (mem_insert _ _) hss, hne hm]
  · exact ext fun _ ↦ and_congr_right fun _ ↦ not_congr mem_domain_singular
  · rintro χ (rfl | rfl) hχ
    · exact subset_rfl
    · exact (hχ.ne ((hne (m := .plural) (by decide)).trans (hne hm).symm)).elim

/-- With two atoms, the plural question is felicitous exactly in the situations that are neither
null nor atomic. -/
theorem felicitous_plural {a b : E} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    felicitous (some .plural) = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} :=
  felicitous_of_ne_singular (E := E) ha hb hab (m := .plural) (by decide)

-- (57a), (65), (66)
theorem not_mem_felicitous_bot (n : Option Number) : (⊥ : E) ∉ felicitous n := by
  rw [felicitous_eq_unblocked_domain]
  exact fun h ↦ (unblocked_subset _ _ _ h).2 rfl

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
example : dayalAns (hamblin (some .singular)) ({mary} : Set Woman) = some (Ici {mary}) :=
  dayalAns_hamblin (mem_domain_singular.2 (isAtom_singleton mary))

-- (49)
example : ¬ IsExhaustivelyResolvable (hamblin (some .singular)) ({mary, sue} : Set Woman) :=
  fun h => not_isAtom_pair (by decide)
    (mem_domain_singular.1 ((isExhaustivelyResolvable_hamblin_iff _ _).1 h))

-- (50)
example : dayalAns (hamblin (some .plural)) ({mary, betty} : Set Woman) =
    some (Ici {mary, betty}) :=
  dayalAns_hamblin <| mem_domain_plural.2 (insert_nonempty _ _).ne_empty

-- (50): Ans-D is defined, the plurality implicature fails
example : dayalAns (hamblin (some .plural)) ({mary} : Set Woman) = some (Ici {mary}) ∧
    ({mary} : Set Woman) ∉ felicitous (some .plural) :=
  ⟨dayalAns_hamblin <| mem_domain_plural.2 (singleton_ne_empty _),
   fun h => ((felicitous_plural (isAtom_singleton mary) (isAtom_singleton sue) mary_ne_sue).symm ▸
     h).2 (isAtom_singleton _)⟩

-- (51)
example : (∀ w : Set Woman, ¬ IsExhaustivelyResolvable (polarWh (some .singular)) w) ∧
    ∀ w : Set Woman, IsExhaustivelyResolvable (polarWh (some .plural)) w ↔ w = univ :=
  ⟨not_isExhaustivelyResolvable_polarWh_singular (isAtom_singleton mary) (isAtom_singleton sue)
    mary_ne_sue,
   isExhaustivelyResolvable_polarWh_plural_iff (isAtom_singleton mary) (isAtom_singleton sue)
    mary_ne_sue⟩

-- (52): Beck and Rullmann's answer to the singular question when John likes Mary and Sue
example : weakAnswer (hamblin (some .singular)) ({mary, sue} : Set Woman) = Ici {mary, sue} ∧
    Ici ({mary, sue} : Set Woman) ∉ hamblin (some .singular) :=
  ⟨weakAnswer_hamblin _ _,
   fun ⟨_, hx, h⟩ => not_isAtom_pair (by decide) (Ici_injective h ▸ mem_domain_singular.1 hx)⟩

/-! ### The chapter's judgments -/

theorem isAtom_coe_iff (s : Finset Woman) : IsAtom (s : Set Woman) ↔ s.card = 1 := by
  rw [Set.isAtom_iff, Finset.card_eq_one]
  exact exists_congr fun _ => Finset.coe_eq_singleton

theorem coe_mem_felicitous_iff (n : Option Number) (s : Finset Woman) :
    (s : Set Woman) ∈ felicitous n ↔
      (n = some .singular → s.card = 1) ∧ (n ≠ some .singular → s ≠ ∅) ∧
        (n ≠ none → n ≠ some .singular → s.card ≠ 1) := by
  rcases n with _ | m
  · simp [felicitous_none, Finset.coe_eq_empty]
  · by_cases hm : m = .singular
    · subst hm
      simp [felicitous_singular, isAtom_coe_iff]
    · rw [felicitous_of_ne_singular (isAtom_singleton mary) (isAtom_singleton sue) mary_ne_sue hm]
      simp [hm, Finset.coe_eq_empty, isAtom_coe_iff]

instance (n : Option Number) (s : Finset Woman) : Decidable ((s : Set Woman) ∈ felicitous n) :=
  decidable_of_iff _ (coe_mem_felicitous_iff n s).symm

-- (41), (42), (65), (66)
theorem rows_agree : ∀ e ∈ Examples.all,
    ∀ n ∈ e.parse? "whNumber"
      [("singular", some .singular), ("plural", some .plural), ("neutral", none)],
      ∀ s ∈ e.parse? "situation"
        ([("none", ∅), ("one", {mary}), ("two", {mary, sue})] : List (String × Finset Woman)),
        (e.judgment = .acceptable ↔ (s : Set Woman) ∈ felicitous n) := by
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
        Coherent {w : Set Woman | IsExhaustivelyResolvable (hamblin none) w} h x) := by
  have hP : {w : Set Woman | IsExhaustivelyResolvable (hamblin none) w}.Nonempty :=
    ⟨{mary}, (isExhaustivelyResolvable_hamblin_iff _ _).2 ⟨trivial, singleton_ne_empty _⟩⟩
  have hP' : {w : Set Woman | IsExhaustivelyResolvable (hamblin none) w}ᶜ.Nonempty :=
    ⟨∅, fun h => ((isExhaustivelyResolvable_hamblin_iff _ _).1 h).2 rfl⟩
  simp only [coherent_iff hP hP']
  decide

end Dayal2016
