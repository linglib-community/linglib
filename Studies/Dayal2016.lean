module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Atoms
public import Mathlib.Data.Set.Lattice.Order
public import Linglib.Data.Examples.Dayal2016
public import Linglib.Syntax.Number.Basic
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Questions.HamblinSet

/-!
# Dayal (2016): Questions

The book's baseline theory, chapter 2, blends the three classic theories of
questions into the account the later chapters build on.
From Hamblin it keeps the denotation, a set of propositions; from Karttunen
the truth requirement, moved out of the denotation into an answerhood
operator, because in scope marking (*What does John think? Where is Mary?*)
the second question must contribute its false members too; from Groenendijk
and Stokhof strong exhaustiveness, obtained by Heim's device of collecting
the worlds with the same answer. Its own contribution is number sensitivity:
*which woman* ranges over the atoms of a Sharvy–Link domain, *which women* and
*who* over the whole domain, and Ans-D returns the true member that entails
every other true member, so a singular question presupposes exactly one
witness and a plural one at least one, while Beck and Rullmann's intersection
operator, being number-blind, cannot draw the distinction. The same operator
makes a polar question with a *wh* phrase unanswerable, and its existential
presupposition is a soft one, deniable only by another speaker, which a cleft
turns hard.

We state the scope-marking argument on a two-place model, the number paradigm
over any atomistic complete lattice, the polar-*wh* and Beck–Rullmann
comparisons, and check the chapter's judgments.

## Implementation notes

* A situation is identified with the plurality the nucleus holds of, so the
  nucleus proposition for `x` is `Set.Ici x`; this builds in the distributivity
  the chapter's entailments assume (*John likes Mary and Betty* entails *John
  likes Mary*).
* The plurality implicature of a plural *wh* is a stated felicity condition
  (`Felicitous`), not part of Ans-D, as in the chapter.

## TODO

* Chapters 3–6: the weak–strong distinction and mention-some answers, pair-list
  and functional answers, embedded and concealed questions, and weak islands
  through maximality are not formalized.

## References

* [V. Dayal, *Questions* (2016)][dayal-2016]
* [V. Dayal, *Locality in WH quantification* (1996)][dayal-1996]
* [V. Dayal, *Scope marking as indirect wh-dependency* (1994)][dayal-1994]
* [L. Karttunen, *Syntax and semantics of questions* (1977)][karttunen-1977]
* [I. Heim, *Interrogative semantics and Karttunen's semantics for know*
  (1994)][heim-1994]
* [J. Groenendijk and M. Stokhof, *Studies on the semantics of questions*
  (1984)][groenendijk-stokhof-1984]
* [S. Beck and H. Rullmann, *A flexible approach to exhaustivity in questions*
  (1999)][beck-rullmann-1999]
* [M. Bittner, *Cross-linguistic semantics for questions* (1998)][bittner-1998]
* [U. Lahiri, *Questions and answers in embedded contexts* (2002)][lahiri-2002]
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

/-! ### Scope marking (34)–(37): the truth requirement leaves the denotation -/

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

/-- (36a): the Hamblin set of *Where is Mary?*. -/
def whereMary : Set (Set World) := range isAt

/-- (34b): *What does John think? Where is Mary?* — the matrix question quantifies over
propositions with `whereMary` as its restriction, the indirect dependency. -/
def scopeMarked : Set (Set World) := think '' whereMary

/-- Mary is in Paris and John thinks she is in London. -/
def w₀ : World := (.paris, .london)

-- (36b), (37c)
theorem trueAnswers_whereMary : trueAnswers whereMary w₀ = {isAt .paris} := by
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, hw⟩
    cases x
    · simp [isAt, w₀] at hw
    · exact mem_singleton _
  · intro hp
    obtain rfl := mem_singleton_iff.1 hp
    exact ⟨⟨.paris, rfl⟩, rfl⟩

theorem trueAnswers_scopeMarked : trueAnswers scopeMarked w₀ = {think (isAt .london)} := by
  ext p
  constructor
  · rintro ⟨⟨q, ⟨x, rfl⟩, rfl⟩, hw⟩
    cases x
    · exact mem_singleton _
    · exact absurd (hw (.london, .london) rfl) (by simp [isAt])
  · intro hp
    obtain rfl := mem_singleton_iff.1 hp
    exact ⟨⟨isAt .london, ⟨.london, rfl⟩, rfl⟩, fun _ hv => hv⟩

-- (35b)
theorem think_london_mem : think (isAt .london) ∈ trueAnswers scopeMarked w₀ := by
  rw [trueAnswers_scopeMarked]
  exact mem_singleton _

-- (36)
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

/-! ### Number (41)–(44), (63): singular *which* ranges over atoms -/

section Number

variable {E : Type*} [CompleteLattice E]

/-- (63): what a *wh* phrase ranges over — singular *which N* the atoms, plural *which N*
and number-neutral *who* and *what* the whole domain. -/
def domain : Number → Set E
  | .singular => {a | IsAtom a}
  | _ => {x | x ≠ ⊥}

theorem domain_of_ne_singular {n : Number} (h : n ≠ .singular) :
    domain n = {x : E | x ≠ ⊥} := by
  cases n <;> first | exact absurd rfl h | rfl

/-- (44)/(63): the Hamblin set of *which N / who does John like?*: a situation is the
plurality John likes, so the member for `x` is `Ici x`. -/
def hamblin (n : Number) : Set (Set E) := Ici '' domain n

theorem trueAnswers_image_Ici (D : Set E) (w : E) :
    trueAnswers (Ici '' D) w = Ici '' {x ∈ D | x ≤ w} := by
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hw⟩
    exact ⟨x, ⟨hx, hw⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hw⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hw⟩

theorem weakAnswer_image_Ici (D : Set E) (w : E) :
    weakAnswer (Ici '' D) w = Ici (sSup {x ∈ D | x ≤ w}) := by
  rw [weakAnswer, trueAnswers_image_Ici, sInter_image, Ici_sSup]

/-! ### Polar questions with a *wh* phrase (51) -/

/-- (51): *Does John like which woman/women?* — each member of the Hamblin set and its
negation. -/
def polarWh (n : Number) : Set (Set E) := hamblin n ∪ compl '' hamblin n

theorem mem_polarWh {n : Number} {p : Set E} :
    p ∈ polarWh n ↔ ∃ x ∈ domain n, Ici x = p ∨ (Ici x)ᶜ = p := by
  rw [polarWh, hamblin, image_image]
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    exacts [⟨x, hx, Or.inl h⟩, ⟨x, hx, Or.inr h⟩]
  · rintro ⟨x, hx, h | h⟩
    exacts [Or.inl ⟨x, hx, h⟩, Or.inr ⟨x, hx, h⟩]

private theorem not_Ici_subset_compl (a c : E) : ¬ Ici c ⊆ (Ici a)ᶜ :=
  fun h => h (show a ⊔ c ∈ Ici c from le_sup_right) (show a ≤ a ⊔ c from le_sup_left)

private theorem not_compl_Ici_subset {a c : E} (ha : a ≠ ⊥) (hc : c ≠ ⊥) :
    ¬ (Ici c)ᶜ ⊆ Ici a :=
  fun h => ha (le_bot_iff.1 (h fun hc' => hc (le_bot_iff.1 hc')))

private theorem atom_of_subset {a c : E} (ha : IsAtom a) (hc : IsAtom c) {p q : Set E}
    (hp : Ici a = p ∨ (Ici a)ᶜ = p) (hq : Ici c = q ∨ (Ici c)ᶜ = q) (h : q ⊆ p) :
    c = a := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact ((hc.le_iff_eq ha.ne_bot).1 (Ici_subset_Ici.1 h)).symm
  · exact (not_compl_Ici_subset ha.ne_bot hc.ne_bot h).elim
  · exact (not_Ici_subset_compl a c h).elim
  · exact (ha.le_iff_eq hc.ne_bot).1 (Ici_subset_Ici.1 (compl_subset_compl.1 h))

-- (51b)
theorem not_isExhaustivelyResolvable_polarWh_singular {a b : E} (ha : IsAtom a) (hb : IsAtom b)
    (hab : a ≠ b) (w : E) : ¬ IsExhaustivelyResolvable (polarWh .singular) w := by
  rintro ⟨q, hq⟩
  obtain ⟨c, hc, hcq⟩ := mem_polarWh.1 hq.1.1
  have key : ∀ x : E, IsAtom x → c = x := fun x hx => by
    by_cases hxw : x ≤ w
    · exact atom_of_subset hx hc (Or.inl rfl) hcq
        (hq.2 ⟨mem_polarWh.2 ⟨x, hx, Or.inl rfl⟩, hxw⟩)
    · exact atom_of_subset hx hc (Or.inr rfl) hcq
        (hq.2 ⟨mem_polarWh.2 ⟨x, hx, Or.inr rfl⟩, hxw⟩)
  exact hab ((key a ha).symm.trans (key b hb))

-- (51c)
theorem isExhaustivelyResolvable_polarWh_plural_iff {a b : E} (ha : IsAtom a) (hb : IsAtom b)
    (hab : a ≠ b) (w : E) : IsExhaustivelyResolvable (polarWh .plural) w ↔ w = ⊤ := by
  have htop : (⊤ : E) ≠ ⊥ := fun h => ha.ne_bot (le_bot_iff.1 (h ▸ le_top))
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨c, hc, hcq⟩ := mem_polarWh.1 hq.1.1
    by_contra hw
    have hqtop : q ⊆ (Ici ⊤)ᶜ :=
      hq.2 ⟨mem_polarWh.2 ⟨⊤, htop, Or.inr rfl⟩, fun h => hw (top_le_iff.1 h)⟩
    rcases hcq with rfl | rfl
    · exact hqtop (show (⊤ : E) ∈ Ici c from le_top) le_rfl
    · rcases eq_or_ne w ⊥ with rfl | hw0
      · have hle : ∀ x : E, IsAtom x → c ≤ x := fun x hx =>
          Ici_subset_Ici.1 (compl_subset_compl.1 (hq.2
            ⟨mem_polarWh.2 ⟨x, hx.ne_bot, Or.inr rfl⟩, fun h => hx.ne_bot (le_bot_iff.1 h)⟩))
        exact hab (((ha.le_iff_eq hc).1 (hle a ha)).symm.trans ((hb.le_iff_eq hc).1 (hle b hb)))
      · exact not_compl_Ici_subset hw0 hc
          (hq.2 ⟨mem_polarWh.2 ⟨w, hw0, Or.inl rfl⟩, le_rfl⟩)
  · rintro rfl
    refine ⟨Ici ⊤, ⟨mem_polarWh.2 ⟨⊤, htop, Or.inl rfl⟩, le_rfl⟩, ?_⟩
    rintro p ⟨hp, hwp⟩
    obtain ⟨x, -, rfl | rfl⟩ := mem_polarWh.1 hp
    · exact Ici_subset_Ici.2 le_top
    · exact (hwp le_top).elim

variable [IsAtomistic E]

theorem sSup_domain_le (n : Number) (w : E) : sSup {x ∈ domain n | x ≤ w} = w := by
  by_cases h : n = .singular
  · subst h
    exact sSup_atoms_le_eq w
  · rw [domain_of_ne_singular h]
    rcases eq_or_ne w ⊥ with rfl | hw
    · rw [show {x ∈ {x : E | x ≠ ⊥} | x ≤ ⊥} = ∅ by ext x; simp [le_bot_iff],
        sSup_empty]
    · have hg : IsGreatest {x ∈ {x : E | x ≠ ⊥} | x ≤ w} w :=
        ⟨⟨hw, le_rfl⟩, fun _ hx => hx.2⟩
      exact hg.isLUB.sSup_eq

-- (52)
theorem weakAnswer_hamblin (n : Number) (w : E) : weakAnswer (hamblin n) w = Ici w := by
  rw [hamblin, weakAnswer_image_Ici, sSup_domain_le]

-- (49), (65), (50), (66)
theorem isExhaustivelyResolvable_hamblin_iff (n : Number) (w : E) :
    IsExhaustivelyResolvable (hamblin n) w ↔ w ∈ domain n := by
  rw [isExhaustivelyResolvable_iff, weakAnswer_hamblin, hamblin, Ici_injective.mem_set_image]

theorem isExhaustivelyResolvable_singular_iff (w : E) :
    IsExhaustivelyResolvable (hamblin .singular) w ↔ IsAtom w :=
  isExhaustivelyResolvable_hamblin_iff _ w

theorem isExhaustivelyResolvable_plural_iff (w : E) :
    IsExhaustivelyResolvable (hamblin .plural) w ↔ w ≠ ⊥ :=
  isExhaustivelyResolvable_hamblin_iff _ w

-- (49c), (50c), (65b), (66b)
theorem dayalAns_hamblin {n : Number} {w : E} (h : w ∈ domain n) :
    dayalAns (hamblin n) w = some (Ici w) :=
  (dayalAns_eq_some_iff _ _).2 <|
    (isStrongestTrueAnswer_iff _ _).2 ⟨⟨w, h, rfl⟩, (weakAnswer_hamblin n w).symm⟩

theorem strongAnswer_hamblin (n : Number) (w : E) : strongAnswer (hamblin n) w = {w} := by
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
theorem dayalStrongAns_hamblin {n : Number} {w : E} (h : w ∈ domain n) :
    dayalStrongAns (hamblin n) w = some {w} :=
  (dayalStrongAns_eq_some_iff _ _).2
    ⟨(isExhaustivelyResolvable_hamblin_iff n w).2 h, (strongAnswer_hamblin n w).symm⟩

/-! ### Felicity (41)–(42), (65)–(66) -/

/-- A *wh* question is felicitous in situation `w` when Ans-D is defined and, for a plural
*wh*, the plurality implicature of its existential presupposition holds. -/
def Felicitous (n : Number) (w : E) : Prop :=
  IsExhaustivelyResolvable (hamblin n) w ∧ (n = .plural → ¬ IsAtom w)

theorem felicitous_singular_iff (w : E) : Felicitous .singular w ↔ IsAtom w := by
  simp [Felicitous, isExhaustivelyResolvable_singular_iff]

theorem felicitous_plural_iff (w : E) : Felicitous .plural w ↔ w ≠ ⊥ ∧ ¬ IsAtom w := by
  simp [Felicitous, isExhaustivelyResolvable_hamblin_iff, domain]

theorem felicitous_general_iff (w : E) : Felicitous .general w ↔ w ≠ ⊥ := by
  simp [Felicitous, isExhaustivelyResolvable_hamblin_iff, domain]

-- (57a), (65), (66)
theorem not_felicitous_bot (n : Number) : ¬ Felicitous n (⊥ : E) := by
  intro h
  have hb := (isExhaustivelyResolvable_hamblin_iff n ⊥).1 h.1
  cases n <;> simp only [domain, mem_ofPred_eq, ne_eq, not_true_eq_false] at hb
  exact hb.ne_bot rfl

end Number

/-! ### Beck and Rullmann's intersection on scales (53) -/

-- (53a), (53b)
theorem isStrongestTrueAnswer_range_Iic {α : Type*} [Preorder α] (t : α) :
    IsStrongestTrueAnswer (range (Iic : α → Set α)) t (Iic t) := by
  refine ⟨⟨⟨t, rfl⟩, le_rfl⟩, ?_⟩
  rintro q ⟨⟨n, rfl⟩, ht⟩
  exact Iic_subset_Iic.2 ht

-- (53c), (53d)
theorem isStrongestTrueAnswer_range_Ici {α : Type*} [Preorder α] (c : α) :
    IsStrongestTrueAnswer (range (Ici : α → Set α)) c (Ici c) := by
  refine ⟨⟨⟨c, rfl⟩, le_rfl⟩, ?_⟩
  rintro q ⟨⟨n, rfl⟩, hc⟩
  exact Ici_subset_Ici.2 hc

/-! ### The chapter's women (44), (49)–(52), (65)–(66) -/

/-- The women of (44). -/
inductive Woman
  | mary
  | sue
  | betty
  deriving DecidableEq, Fintype

open Woman

private theorem not_isAtom_pair {x y : Woman} (h : x ≠ y) : ¬ IsAtom ({x, y} : Set Woman) := by
  rw [isAtom_iff]
  rintro ⟨z, hz⟩
  have hx : x ∈ ({z} : Set Woman) := hz ▸ mem_insert x {y}
  have hy : y ∈ ({z} : Set Woman) := hz ▸ mem_insert_of_mem x (mem_singleton y)
  exact h ((mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)

-- (49)
theorem ex49 : dayalAns (hamblin .singular) ({mary} : Set Woman) = some (Ici {mary}) :=
  dayalAns_hamblin (isAtom_singleton mary)

-- (49)
theorem ex49_two : ¬ IsExhaustivelyResolvable (hamblin .singular) ({mary, sue} : Set Woman) :=
  fun h => not_isAtom_pair (by decide) ((isExhaustivelyResolvable_singular_iff _).1 h)

-- (50)
theorem ex50 : dayalAns (hamblin .plural) ({mary, betty} : Set Woman) = some (Ici {mary, betty}) :=
  dayalAns_hamblin (insert_nonempty _ _).ne_empty

-- (50)
theorem ex50_one :
    dayalAns (hamblin .plural) ({mary} : Set Woman) = some (Ici {mary}) ∧
      ¬ Felicitous .plural ({mary} : Set Woman) :=
  ⟨dayalAns_hamblin (singleton_ne_empty _),
   fun h => ((felicitous_plural_iff _).1 h).2 (isAtom_singleton _)⟩

-- (51)
theorem ex51 :
    (∀ w : Set Woman, ¬ IsExhaustivelyResolvable (polarWh .singular) w) ∧
      ∀ w : Set Woman, IsExhaustivelyResolvable (polarWh .plural) w ↔ w = univ :=
  have h : ({mary} : Set Woman) ≠ {sue} :=
    fun h => (by decide : mary ≠ sue) (singleton_eq_singleton_iff.1 h)
  ⟨not_isExhaustivelyResolvable_polarWh_singular (isAtom_singleton mary) (isAtom_singleton sue) h,
   isExhaustivelyResolvable_polarWh_plural_iff (isAtom_singleton mary) (isAtom_singleton sue) h⟩

-- (52), (49)
theorem ex52 :
    weakAnswer (hamblin .singular) ({mary, sue} : Set Woman) = Ici {mary, sue} ∧
      Ici ({mary, sue} : Set Woman) ∉ hamblin .singular :=
  ⟨weakAnswer_hamblin _ _,
   fun ⟨_, hx, h⟩ => not_isAtom_pair (by decide) (Ici_injective h ▸ hx)⟩

/-! ### The chapter's judgments -/

/-- The *wh* phrase of a row. -/
def number : String → Option Number
  | "singular" => some .singular
  | "plural" => some .plural
  | "neutral" => some .general
  | _ => none

/-- The situation of a row, as the plurality liked or seen. -/
def situation : String → Option (Finset Woman)
  | "none" => some ∅
  | "one" => some {mary}
  | "two" => some {mary, sue}
  | _ => none

theorem isAtom_coe_iff (s : Finset Woman) : IsAtom (s : Set Woman) ↔ s.card = 1 := by
  rw [Set.isAtom_iff, Finset.card_eq_one]
  exact exists_congr fun _ => Finset.coe_eq_singleton

theorem felicitous_coe_iff (n : Number) (s : Finset Woman) :
    Felicitous n (s : Set Woman) ↔
      (n = .singular → s.card = 1) ∧ (n ≠ .singular → s ≠ ∅) ∧
        (n = .plural → s.card ≠ 1) := by
  unfold Felicitous
  rw [isExhaustivelyResolvable_hamblin_iff]
  by_cases h : n = .singular
  · subst h
    simp [domain, isAtom_coe_iff]
  · rw [domain_of_ne_singular h]
    simp [h, Finset.coe_eq_empty, isAtom_coe_iff]

instance (n : Number) (s : Finset Woman) : Decidable (Felicitous n (s : Set Woman)) :=
  decidable_of_iff _ (felicitous_coe_iff n s).symm

-- (41), (42), (65), (66)
theorem rows_agree :
    ∀ e ∈ Examples.all, ∀ (n : Number) (s : Finset Woman),
      (e.feature? "whNumber").bind number = some n →
      (e.feature? "situation").bind situation = some s →
      (e.judgment = .acceptable ↔ Felicitous n (s : Set Woman)) := by
  decide

-- (57), (59)
theorem existence_rows :
    ∀ e ∈ Examples.all, ∀ v, e.feature? "existence" = some v →
      (e.judgment = .acceptable ↔
        e.feature? "cleft" = some "false" ∧
          (v = "suspended" ∨ e.feature? "speaker" = some "other")) := by
  decide

end Dayal2016
