module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Data.Examples.Belnap1982
public import Studies.Karttunen1977

/-!
# Belnap (1982): Questions and Answers in Montague Grammar

A question denotes its possible answers on Hamblin's scheme, the answers true at a world on
Bennett's, and the true propositions that jointly make up its one answer on Karttunen's. Under
the Assumption that a proposition answering at some world answers wherever it is true, the first
two schemes are intertranslatable, and the third commits the Unique Answer Fallacy. To know a
question is to know some answer to it, which yields a necessary test for answerhood.

## Main statements

* `exists_eq_trueAnswers_iff`: the answers at each world are the true members of a Hamblin set
  exactly under the Assumption (p. 173).
* `weakAnswer_mem_iff_of_antichain`: Karttunen's answer is an answer exactly when the true answer
  is unique (p. 174).
* `InferenceFails.notMem`: the Distributivity Test (p. 177).
* `knowsSomeAnswer_iff_knows`: on unique-answer questions the Distributivity Principle is
  Karttunen's postulate for *know*.
* `trueAnswers_quantifyIn_the`: *whether the king of France is bald* has no true answer (p. 181).

## Implementation notes

A question is its Hamblin set, with Bennett's denotation `Question.trueAnswers` and Karttunen's
answer `Question.weakAnswer`, and the Distributivity Principle is `Question.KnowsSomeAnswer`. The
inquisitive `Question.alt` keeps only maximal answers, and so loses *three apples* beside *some
apples* (`alt_biSup_ofSet_basket`, p. 172).

## Errata

* The two definitions of presupposition can coincide without the Assumption, against p. 176
  (`exists_presuppositions_eq_not_assumption`).
* The premise added on p. 192 must be known to Peter (`not_knowsSomeAnswer_of_presupposition`).

## TODO

* Multiple *which* (§4), *where*, *who* and *what* (§5), and the scope readings of §3.

## References

* [belnap-1982]
* [bennett-1977]
* [hamblin-1973b]
* [karttunen-1977]
-/

@[expose] public section

namespace Belnap1982

open Question Quantifier

variable {W E : Type*}

/-! ### Hamblin's and Bennett's schemes (§2.2) -/

section Schemes

variable {Ans : W → Set (Set W)}

/-- Answers satisfy the Assumption when a proposition answering at some world answers at every
world where it is true (p. 173). -/
def Assumption (Ans : W → Set (Set W)) : Prop := ∀ ⦃w v p⦄, p ∈ Ans w → v ∈ p → p ∈ Ans v

theorem assumption_trueAnswers (H : Set (Set W)) : Assumption (trueAnswers H) :=
  fun _ _ _ hp hv ↦ ⟨hp.1, hv⟩

theorem trueAnswers_iUnion (hT : ∀ w, ∀ p ∈ Ans w, w ∈ p) (hA : Assumption Ans) :
    trueAnswers (⋃ w, Ans w) = Ans := by
  ext w p
  simp only [mem_trueAnswers, Set.mem_iUnion]
  exact ⟨fun ⟨⟨_, hp⟩, hw⟩ ↦ hA hp hw, fun hp ↦ ⟨⟨w, hp⟩, hT w p hp⟩⟩

/-- Answers at each world are the true members of a Hamblin set exactly when they are true and
satisfy the Assumption. -/
theorem exists_eq_trueAnswers_iff :
    (∃ H, Ans = trueAnswers H) ↔ (∀ w, ∀ p ∈ Ans w, w ∈ p) ∧ Assumption Ans := by
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨fun _ _ hp ↦ hp.2, assumption_trueAnswers H⟩
  · rintro ⟨hT, hA⟩
    exact ⟨_, (trueAnswers_iUnion hT hA).symm⟩

theorem possibleAnswer_iff_iff_assumption (hT : ∀ w, ∀ p ∈ Ans w, w ∈ p) :
    (∀ p, (p.Nonempty ∧ ∀ w ∈ p, p ∈ Ans w) ↔ ∃ w, p ∈ Ans w) ↔ Assumption Ans := by
  refine ⟨fun h w v p hp hv ↦ ((h p).2 ⟨w, hp⟩).2 v hv, fun hA p ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨⟨w, hw⟩, h⟩
    exact ⟨w, h w hw⟩
  · rintro ⟨w, hp⟩
    exact ⟨⟨w, hT w p hp⟩, fun v hv ↦ hA hp hv⟩

theorem presuppositions_eq_iff (hT : ∀ w, ∀ p ∈ Ans w, w ∈ p) :
    {r : Set W | ∀ w, ∀ p ∈ Ans w, p ⊆ r} = {r | ∀ w, (Ans w).Nonempty → w ∈ r} ↔
      ∀ w, ∀ p ∈ Ans w, p ⊆ {v | (Ans v).Nonempty} := by
  refine ⟨fun h w p hp ↦ (Set.ext_iff.1 h {v | (Ans v).Nonempty}).2 (fun _ hw ↦ hw) w p hp,
    fun h ↦ ?_⟩
  ext r
  exact ⟨fun hr w ⟨p, hp⟩ ↦ hr w p hp (hT w p hp), fun hr w p hp v hv ↦ hr v (h w p hp hv)⟩

theorem presuppositions_eq (hT : ∀ w, ∀ p ∈ Ans w, w ∈ p) (hA : Assumption Ans) :
    {r : Set W | ∀ w, ∀ p ∈ Ans w, p ⊆ r} = {r | ∀ w, (Ans w).Nonempty → w ∈ r} :=
  (presuppositions_eq_iff hT).2 fun _ p hp _ hv ↦ ⟨p, hA hp hv⟩

theorem exists_presuppositions_eq_not_assumption :
    ∃ Ans : Bool → Set (Set Bool), (∀ w, ∀ p ∈ Ans w, w ∈ p) ∧
      {r | ∀ w, ∀ p ∈ Ans w, p ⊆ r} = {r | ∀ w, (Ans w).Nonempty → w ∈ r} ∧
        ¬Assumption Ans := by
  have hT : ∀ w, ∀ p ∈ ({if w then Set.univ else {false}} : Set (Set Bool)), w ∈ p := by
    rintro (_ | _) p rfl <;> simp
  refine ⟨fun w ↦ {if w then Set.univ else {false}}, hT,
    (presuppositions_eq_iff hT).2 fun _ _ _ v _ ↦ Set.singleton_nonempty _, fun h ↦ ?_⟩
  have := h (w := true) (v := false) (p := Set.univ) (by simp) trivial
  simp only [Bool.false_eq_true, ite_false, Set.mem_singleton_iff] at this
  exact absurd (this ▸ Set.mem_univ true) (by simp)

end Schemes

/-! ### The Unique Answer Fallacy (§2.2) -/

/-- On an antichain of answers, Karttunen's answer is an answer exactly when the true answer is
unique. -/
theorem weakAnswer_mem_iff_of_antichain {H : Set (Set W)} (hH : IsAntichain (· ⊆ ·) H) (w : W) :
    weakAnswer H w ∈ H ↔ ∃ p, trueAnswers H w = {p} :=
  (isExhaustivelyResolvable_iff H w).symm.trans
    (isExhaustivelyResolvable_iff_of_antichain H w hH)

/-- The two stations of the gas example. -/
inductive Station
  | a
  | b
  deriving DecidableEq

/-- The proposition that station `s` is open on Sunday, over worlds given by the open stations. -/
def isOpen (s : Station) : Set (Set Station) := {w | s ∈ w}

/-- *Where is a place at which I can get gas on a Sunday?* (p. 172) has an answer for each
station. -/
def gas : Set (Set (Set Station)) := Set.range isOpen

theorem isOpen_a_ne_b : isOpen .a ≠ isOpen .b := fun h ↦ by
  have := congrArg (({Station.a} : Set Station) ∈ ·) h
  simp [isOpen] at this

theorem isAntichain_gas : IsAntichain (· ⊆ ·) gas := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hne hsub
  exact hne (congrArg isOpen (hsub (Set.mem_singleton s) : t ∈ ({s} : Set Station)).symm)

theorem trueAnswers_gas_univ : trueAnswers gas Set.univ = {isOpen .a, isOpen .b} := by
  ext p
  refine ⟨fun ⟨⟨s, hs⟩, _⟩ ↦ ?_, ?_⟩
  · cases s <;> simp [← hs]
  · rintro (rfl | rfl) <;> exact ⟨⟨_, rfl⟩, trivial⟩

theorem gas_unique_answer_fallacy :
    trueAnswers gas Set.univ = {isOpen .a, isOpen .b} ∧ weakAnswer gas Set.univ ∉ gas := by
  refine ⟨trueAnswers_gas_univ, fun h ↦ ?_⟩
  obtain ⟨p, hp⟩ := (weakAnswer_mem_iff_of_antichain isAntichain_gas _).1 h
  rw [trueAnswers_gas_univ] at hp
  have ha : isOpen .a ∈ ({p} : Set _) := hp ▸ Or.inl rfl
  have hb : isOpen .b ∈ ({p} : Set _) := hp ▸ Or.inr rfl
  exact isOpen_a_ne_b (ha.trans hb.symm)

/-- *What's in the basket?* (p. 172), over worlds given by the number of apples in the basket,
with the answers *some apples* and *three apples*. -/
def basket : Set (Set ℕ) := {{n | 0 < n}, {3}}

theorem basket_answers :
    trueAnswers basket 3 = basket ∧ ({n | 0 < n} : Set ℕ) ≠ {3} ∧ weakAnswer basket 3 ∈ basket := by
  have hw : weakAnswer basket 3 = {3} := by
    ext n
    simp only [mem_weakAnswer, basket, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, Set.mem_ofPred_eq, true_implies]
    omega
  refine ⟨?_, fun h ↦ ?_, hw ▸ Or.inr rfl⟩
  · ext p
    simp only [mem_trueAnswers, basket, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact And.left
    · rintro (rfl | rfl) <;> simp
  · have := congrArg (1 ∈ ·) h
    simp at this

theorem alt_biSup_ofSet_basket : alt (⨆ p ∈ basket, ofSet p) = {{n | 0 < n}} := by
  rw [alt_biSup_ofSet_eq ⟨_, Or.inl rfl⟩]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun ⟨hp, hmax⟩ ↦ hp.resolve_right fun h ↦ ?_, ?_⟩
  · subst h
    have := hmax (Or.inl rfl) (by simp)
    exact absurd (this (show 1 ∈ {n : ℕ | 0 < n} from Nat.one_pos)) (by simp)
  · rintro rfl
    refine ⟨Or.inl rfl, fun q hq hle ↦ ?_⟩
    rcases hq with rfl | rfl
    · exact le_rfl
    · exact absurd (hle (show 1 ∈ {n : ℕ | 0 < n} from Nat.one_pos)) (by simp)

theorem fallacy_rows :
    ((∃ p ∈ trueAnswers gas Set.univ, ∃ q ∈ trueAnswers gas Set.univ, p ≠ q) ↔
      Examples.gas.feature? "answers" = some "multiple, each full and complete and true") ∧
    ((∃ p ∈ trueAnswers basket 3, ∃ q ∈ trueAnswers basket 3, p ≠ q) ↔
      Examples.basket.feature? "answers" = some "multiple, each full and complete and true") := by
  refine ⟨iff_of_true ?_ rfl, iff_of_true ?_ rfl⟩
  · rw [trueAnswers_gas_univ]
    exact ⟨_, Or.inl rfl, _, Or.inr rfl, isOpen_a_ne_b⟩
  · rw [basket_answers.1]
    exact ⟨_, Or.inl rfl, _, Or.inr rfl, basket_answers.2.1⟩

/-! ### The Distributivity Principle and Test (§2.4) -/

section Distributivity

variable {H : Set (Set W)} {p : Set W} {w : W} {K : SetRel W W}

/-- The inference from knowing that `p` to knowing `H` fails when an agent with factive knowledge
knows that `p` without knowing some answer to `H` (p. 177). -/
def InferenceFails (p : Set W) (H : Set (Set W)) : Prop :=
  ∃ (K : SetRel W W) (w : W), K.IsRefl ∧ w ∈ K.core p ∧ ¬KnowsSomeAnswer H w K

/-- A proposition for which the inference fails is not an answer. -/
theorem InferenceFails.notMem (h : InferenceFails p H) : p ∉ H := by
  obtain ⟨K, w, hK, hw, hn⟩ := h
  exact fun hp ↦ hn (knowsSomeAnswer_of_mem hp hw)

private def alsoPossible (v : W) : SetRel W W := {q | q.1 = q.2 ∨ q.2 = v}

private instance (v : W) : (alsoPossible v).IsRefl := ⟨fun _ ↦ Or.inl rfl⟩

private theorem mem_core_alsoPossible {v : W} {q : Set W} :
    w ∈ (alsoPossible v).core q ↔ w ∈ q ∧ v ∈ q :=
  ⟨fun h ↦ ⟨h (Or.inl rfl), h (Or.inr rfl)⟩,
    fun ⟨hw, hv⟩ u hu ↦ hu.elim (fun h : w = u ↦ h ▸ hw) fun h : u = v ↦ h ▸ hv⟩

private theorem inferenceFails_of {v : W} (hw : w ∈ p) (hv : v ∈ p)
    (hn : ∀ q ∈ trueAnswers H w, v ∉ q) : InferenceFails p H :=
  ⟨alsoPossible v, w, inferInstance, mem_core_alsoPossible.2 ⟨hw, hv⟩,
    fun ⟨q, hq, hk⟩ ↦ hn q hq (mem_core_alsoPossible.1 hk).2⟩

/-- On a question with a unique true answer, knowing some answer is knowing the question by
Karttunen's postulate. -/
theorem knowsSomeAnswer_iff_knows (h : trueAnswers H w = {p}) :
    KnowsSomeAnswer H w K ↔ Karttunen1977.Knows H w K := by
  simp [Karttunen1977.Knows, knowsSomeAnswer_iff_knowsAnswer h, h]

theorem knowsSomeAnswer_not_knows :
    ∃ K : SetRel (Set Station) (Set Station), K.IsRefl ∧ KnowsSomeAnswer gas Set.univ K ∧
      ¬Karttunen1977.Knows gas Set.univ K := by
  refine ⟨alsoPossible {Station.a}, inferInstance,
    ⟨isOpen .a, ⟨⟨_, rfl⟩, trivial⟩, mem_core_alsoPossible.2 ⟨trivial, rfl⟩⟩,
    fun ⟨hk, _⟩ ↦ ?_⟩
  have := (mem_weakAnswer gas Set.univ).1 (mem_core_alsoPossible.1 hk).2 (isOpen .b) ⟨_, rfl⟩
    trivial
  simp [isOpen] at this

theorem test_only_necessary :
    ¬InferenceFails (weakAnswer gas Set.univ) gas ∧ weakAnswer gas Set.univ ∉ gas := by
  refine ⟨fun ⟨K, w, hK, hw, hn⟩ ↦ hn ?_, gas_unique_answer_fallacy.2⟩
  exact knowsSomeAnswer_of_mem ⟨.a, rfl⟩
    (SetRel.core_subset_core (weakAnswer_subset gas Set.univ ⟨.a, rfl⟩ trivial) hw)

end Distributivity

/-! ### Quantifying into questions (§3) -/

section QuantifyingIn

variable {cn : E → Set W} {φ : E → Set (Set W)} {O : Set W} {w : W}

/-- An answer to the question introducing `det` `cn` into an open question with answers `φ y` says,
of a property `P` and a function `f`, that `det` `cn`s are `P`s and that `f` gives a true answer
for each `P`, which is a `cn` (T12–14, p. 186). -/
def quantifyIn (det : GQ E) (cn : E → Set W) (φ : E → Set (Set W)) : Set (Set W) :=
  {O | ∃ (P : W → Set E) (f : W → E → Set W), O = {w | det (w ∈ cn ·) (· ∈ P w) ∧
    ∀ y ∈ P w, w ∈ cn y ∧ f w y ∈ φ y ∧ w ∈ f w y}}

theorem exists_mem_of_mem_trueAnswers_every (hO : O ∈ trueAnswers (quantifyIn GQ.every cn φ) w)
    {y : E} (hy : w ∈ cn y) : ∃ p ∈ φ y, w ∈ p := by
  obtain ⟨⟨P, f, rfl⟩, hdet, hall⟩ := hO
  obtain ⟨-, hf, hw⟩ := hall y (hdet y hy)
  exact ⟨_, hf, hw⟩

/-- A question introducing *the* `cn` has no true answer where nothing is a `cn`. -/
theorem trueAnswers_quantifyIn_the (h : ∀ y, w ∉ cn y) :
    trueAnswers (quantifyIn GQ.the cn φ) w = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨⟨_, _, hO⟩, hw⟩ ↦ by
    subst hO
    obtain ⟨⟨x, hx, -⟩, -⟩ := hw
    exact h x ((hx x).2 rfl)

/-- *The present king of France*, over worlds with a king who is bald or not, or with none. -/
def kingOfFrance : Unit → Set (Option Bool) := fun _ ↦ Set.range some

/-- *Whether he₀ is bald* has the answers *he₀ is bald* and *he₀ is not bald*. -/
def whetherBald : Unit → Set (Set (Option Bool)) := fun _ ↦ {{some true}, {some false}}

theorem king_row :
    trueAnswers (quantifyIn GQ.the kingOfFrance whetherBald) none = ∅ ↔
      Examples.king.feature? "status" = some "no true answers" :=
  iff_of_true (trueAnswers_quantifyIn_the fun _ ↦ by simp [kingOfFrance]) rfl

/-- On the external view of answerhood, `O` says only that each `P` has its `f`-answer, and it
answers at `w` when the `P`s are `det` `cn`s there (p. 181). -/
def externalAnswers (det : GQ E) (cn : E → Set W) (φ : E → Set (Set W)) (w : W) :
    Set (Set W) :=
  {O | w ∈ O ∧ ∃ (P : Set E) (f : E → Set W), O = {v | ∀ y ∈ P, v ∈ f y} ∧
    det (w ∈ cn ·) (· ∈ P) ∧ ∀ y ∈ P, w ∈ cn y ∧ f y ∈ φ y}

theorem not_assumption_externalAnswers :
    ¬Assumption (externalAnswers GQ.some (fun _ : Unit ↦ ({true} : Set Bool))
      fun _ ↦ {Set.univ}) := fun h ↦ by
  have hmem : Set.univ ∈ externalAnswers GQ.some (fun _ : Unit ↦ ({true} : Set Bool))
      (fun _ ↦ {Set.univ}) true :=
    ⟨trivial, {()}, fun _ ↦ Set.univ, by simp, ⟨(), rfl, rfl⟩, fun _ _ ↦ ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, -, -, ⟨_, hx, -⟩, -⟩ := h hmem (Set.mem_univ false)
  exact Bool.false_ne_true hx

end QuantifyingIn

/-! ### Singular *which* (§4) and the test examples (§2.4) -/

section SingularWhich

variable {η φ : E → Set W} {w : W} {K : SetRel W W}

/-- The proposition that the `η` that `φ` is `x`, with Russellian *the* (p. 192). -/
def theAnswer (η φ : E → Set W) (x : E) : Set W := {w | GQ.the (fun y ↦ w ∈ η y ∧ w ∈ φ y) (· = x)}

theorem mem_theAnswer {x : E} : w ∈ theAnswer η φ x ↔ ∀ y, w ∈ η y ∧ w ∈ φ y ↔ y = x :=
  ⟨fun ⟨_, h, hx⟩ ↦ hx ▸ h, fun h ↦ ⟨x, h, rfl⟩⟩

/-- The singular *which* question has an answer *the `η` that `φ` is `x`* for each `x` (T17,
p. 192). -/
def singularWhich (η φ : E → Set W) : Set (Set W) := Set.range (theAnswer η φ)

theorem trueAnswers_singularWhich_eq_empty {x y : E} (hxy : x ≠ y) (hx : w ∈ η x ∧ w ∈ φ x)
    (hy : w ∈ η y ∧ w ∈ φ y) : trueAnswers (singularWhich η φ) w = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨⟨_, hz⟩, hw⟩ ↦ hxy <| by
    subst hz
    exact ((mem_theAnswer.1 hw x).1 hx).trans ((mem_theAnswer.1 hw y).1 hy).symm

theorem inferenceFails_of_ne {x y : E} (hxy : x ≠ y) (hx : w ∈ η x ∧ w ∈ φ x)
    (hy : w ∈ η y ∧ w ∈ φ y) : InferenceFails (φ x) (singularWhich η φ) :=
  inferenceFails_of hx.2 hx.2 (by simp [trueAnswers_singularWhich_eq_empty hxy hx hy])

theorem knowsSomeAnswer_of_knows_presupposition [K.IsRefl] {x : E} (hx : w ∈ K.core (η x ∩ φ x))
    (hpre : w ∈ K.core (⋃₀ singularWhich η φ)) : KnowsSomeAnswer (singularWhich η φ) w K :=
  knowsSomeAnswer_of_mem ⟨x, rfl⟩ fun v hv ↦ by
    obtain ⟨_, ⟨y, rfl⟩, hvy⟩ := hpre hv
    exact (mem_theAnswer.1 hvy x).1 (hx hv) ▸ hvy

/-- The individuals of the test examples. -/
inductive Person
  | john
  | bill
  deriving DecidableEq

/-- A world of the test examples fixes who kicked Sam, whom Mary loves, and whether China is
populous. -/
structure World where
  /-- The people who kicked Sam. -/
  kickers : Set Person
  /-- The men Mary loves. -/
  lovedByMary : Set Person
  /-- Whether China is populous. -/
  chinaPopulous : Prop

/-- The proposition that `y` kicked Sam. -/
def kickedSam (y : Person) : Set World := {w | y ∈ w.kickers}

/-- The proposition that Mary loves `y`. -/
def maryLoves (y : Person) : Set World := {w | y ∈ w.lovedByMary}

/-- *China is populous*. -/
def chinaIsPopulous : Set World := {w | w.chinaPopulous}

/-- *A redhead kicked Sam*, where both people are redheads. -/
def aRedheadKickedSam : Set World := {w | w.kickers.Nonempty}

/-- *Which person kicked Sam?* (1). -/
def whichPersonKickedSam : Set (Set World) := singularWhich (fun _ ↦ Set.univ) kickedSam

/-- *Which man Mary loves* (p. 192). -/
def whichManMaryLoves : Set (Set World) := singularWhich (fun _ ↦ Set.univ) maryLoves

private theorem billAlone_notMem {q : Set World}
    (hq : q ∈ trueAnswers whichPersonKickedSam ⟨{Person.john}, ∅, True⟩) :
    (⟨{Person.bill}, ∅, True⟩ : World) ∉ q := by
  obtain ⟨⟨x, rfl⟩, hw⟩ := hq
  intro hv
  have h1 := (mem_theAnswer.1 hw .john).1 ⟨trivial, rfl⟩
  have h2 := (mem_theAnswer.1 hv .bill).1 ⟨trivial, rfl⟩
  exact absurd (h1.trans h2.symm) (by decide)

theorem test_rows :
    (InferenceFails chinaIsPopulous whichPersonKickedSam ↔
      Examples.china.judgment = .acceptable) ∧
    (InferenceFails aRedheadKickedSam whichPersonKickedSam ↔
      Examples.redhead.judgment = .acceptable) ∧
    (InferenceFails (theAnswer (fun _ ↦ Set.univ) kickedSam .john) whichPersonKickedSam ↔
      Examples.john.judgment = .acceptable) ∧
    (InferenceFails (maryLoves .john) whichManMaryLoves ↔
      Examples.mary.judgment = .acceptable) := by
  refine ⟨iff_of_true (inferenceFails_of (w := (⟨{Person.john}, ∅, True⟩ : World))
      (v := ⟨{Person.bill}, ∅, True⟩) trivial trivial fun _ ↦ billAlone_notMem) rfl,
    iff_of_true (inferenceFails_of (w := (⟨{Person.john}, ∅, True⟩ : World))
      (v := ⟨{Person.bill}, ∅, True⟩) ⟨.john, rfl⟩ ⟨.bill, rfl⟩ fun _ ↦ billAlone_notMem) rfl,
    iff_of_false (fun h ↦ h.notMem ⟨_, rfl⟩) (by decide), iff_of_true ?_ rfl⟩
  exact inferenceFails_of_ne (η := fun _ ↦ Set.univ) (φ := maryLoves)
    (w := (⟨∅, {Person.john, Person.bill}, True⟩ : World)) (y := .bill) (by decide)
    ⟨trivial, Or.inl rfl⟩ ⟨trivial, Or.inr rfl⟩

theorem kickedSam_notMem : kickedSam .john ∉ whichPersonKickedSam :=
  (inferenceFails_of_ne (η := fun _ ↦ Set.univ) (φ := kickedSam) (x := .john)
    (w := (⟨{Person.john, Person.bill}, ∅, True⟩ : World)) (y := .bill) (by decide)
    ⟨trivial, Or.inl rfl⟩ ⟨trivial, Or.inr rfl⟩).notMem

theorem not_knowsSomeAnswer_of_presupposition :
    ∃ (K : SetRel World World) (w : World), K.IsRefl ∧ w ∈ K.core (maryLoves .john) ∧
      w ∈ ⋃₀ whichManMaryLoves ∧ ¬KnowsSomeAnswer whichManMaryLoves w K := by
  refine ⟨alsoPossible ⟨∅, {Person.john, Person.bill}, True⟩, ⟨∅, {Person.john}, True⟩,
    inferInstance, mem_core_alsoPossible.2 ⟨Set.mem_singleton _, Or.inl rfl⟩,
    ⟨_, ⟨.john, rfl⟩, mem_theAnswer.2 fun y ↦ by simp [maryLoves]⟩, ?_⟩
  rintro ⟨_, ⟨⟨x, rfl⟩, hw⟩, hk⟩
  have h1 := (mem_theAnswer.1 hw .john).1 ⟨trivial, rfl⟩
  have h2 := (mem_theAnswer.1 (mem_core_alsoPossible.1 hk).2 .bill).1 ⟨trivial, Or.inr rfl⟩
  exact absurd (h1.trans h2.symm) (by decide)

end SingularWhich

end Belnap1982
