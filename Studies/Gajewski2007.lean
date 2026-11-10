module

public import Linglib.Fragments.English.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Semantics.Presupposition.TwoDimensional
public import Linglib.Logic.Modal.Defs
public import Linglib.Data.Examples.Gajewski2007
public import Linglib.Data.Examples.Readers

/-!
# Gajewski (2007): Neg-Raising and Polarity

Gajewski gives a presuppositional account of neg-raising and argues for it from the licensing of
strict negative polarity items. Following Bartsch, a neg-raising predicate such as *think*
presupposes that its subject is settled about the complement, so its negation
[is the predicate over the negated complement](##NegRaising.posExt_negation). Strict NPIs such as
punctual *until* and *in years* need an anti-additive environment, as Zwarts proposes, and the
presupposition makes a negated neg-raising predicate
[anti-additive](##NegRaising.isAntiAdditive_posExt_negation) where a negated universal is not.
Since the presupposition of a complement projects into the subject's beliefs whatever the
attitude, the negation lowers through *think* into the complement of *want* [but not through
*want* into the complement of *think*](##Gajewski2007.not_isAntiAdditive_posExt_notStack), the
asymmetry of stacked neg-raising predicates that Horn reports. With each environment read as a
licenser of the library's licensing theory, the theory [admits the strict NPI of each example
exactly where the paper accepts it](##Gajewski2007.judgments_predicted), superlatives aside.

## Implementation notes

* The neg-raising predicate of Appendix 2 is the library's `NegRaising.box`, over a modal base
  and the worlds into which the complement's presupposition projects. Its negation over a
  presuppositionless complement is `NegRaising.negation`, the licenser of
  `LicensingContext.superordinateNegation`.
* An environment is a sentence as a function of the proposition in the NPI's clause, and its
  anti-additivity is `IsAntiAdditive` of the truth set (`Trivalent.posExt`): standard entailment,
  which Appendix 1 argues is the relevant notion. This is how `PolarityItem.Licenser.Holds` reads a
  presupposing licenser, so each environment is a `Licenser` and licensing is the library's
  `Licenser.Admits`.
* The schematic environments NOT(SOME(_)) and NOT(EVERY(_)) are the operators the library gives
  *nobody* and *doubt*, and `Environment.licenser` cites those. *Only DP*, adversatives,
  conditional antecedents and superlatives are the library's named contexts.
* The stressed reading without neg-raising cancels the presupposition with Beaver and Krahmer's
  assertion operator, so it negates `fun w ↦ Trivalent.ofProp (p w = .true)`.
* The model (7) of Appendix 2 lists no belief worlds for the higher subject. The frame here adds
  one, at which the lower subject is opinionated, so that the projected presupposition is not
  vacuous.
* *No one thinks* is the negated Weak Kleene existential `Trivalent.existsWeak` over the subtype
  of people, which projects the excluded middle universally, and negated *know* is the substrate's
  two-dimensional `ConventionalImplicature.TwoDim.negFactive` over a presuppositionless
  complement.
* The complement in the NPI's clause is presuppositionless, a set of worlds.

## TODO

* The appendix to §2 explains why *it's not true that* fails to license: *true* cancels the
  complement's presupposition, and disjunction projects presuppositions as in
  Karttunen and Peters. Formalizing it needs complements with presuppositions, and the paper
  calls the explanation technical and incomplete.
* The Romance n-words of A.3 are not formalized.

## References

* [gajewski-2007]
* [bartsch-1973]
* [zwarts-1998]
* [von-fintel-1999]
* [horn-1978]
* [karttunen-peters-1979]
* [heim-1983]
* [heim-1992]
* [beaver-krahmer-2001]
-/

@[expose] public section

namespace Gajewski2007

open ModalLogic Presupposition ConventionalImplicature NaturalLogic PolarityItem NegRaising SetRel

variable {W : Type*}

variable {R H : SetRel W W} {w : W}

/-! ### The environments EVERY(NOT(_)) and NOT(EVERY(_)) ((48)–(56)) -/

/-- The EVERY of (92) and (110) is universal quantification with existential import over the
successors of a world, as a function on propositions. -/
def every (R : SetRel W W) (s : Set W) : Set W := R.dom ∩ R.core s

@[simp] theorem mem_every {s : Set W} :
    w ∈ every R s ↔ (∃ u, w ~[R] u) ∧ ∀ ⦃u⦄, w ~[R] u → u ∈ s := .rfl

theorem every_inter (R : SetRel W W) (p q : Set W) : every R (p ∩ q) = every R p ∩ every R q := by
  rw [every, every, every, core_inter, Set.inter_inter_distrib_left]

@[simp] theorem every_empty (R : SetRel W W) : every R ∅ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨⟨_, hu⟩, h⟩ ↦ h hu

-- (92a)
theorem isAntiAdditive_every {V : Type*} {g : Set V → Set W} (hg : IsAntiAdditive g) :
    IsAntiAdditive (every R ∘ g) :=
  hg.map_inf_comp (every_inter R)

-- (2)
theorem not_compl_core_subset :
    ¬ ∀ (W : Type) (R : SetRel W W) (p : Set W), (R.core p)ᶜ ⊆ R.core pᶜ :=
  fun h ↦ h Bool .univ {true} (fun hb ↦ by simpa using @hb false trivial)
    (Set.mem_univ (true, true)) rfl

-- (51b), (53), (65)
theorem not_isAntiAdditive_compl_core :
    ¬ IsAntiAdditive fun p : Set Bool ↦ (SetRel.core (.univ : SetRel Bool Bool) p)ᶜ := by
  rw [isAntiAdditive_iff_mem]
  intro h
  refine (h {true} {false} true).2 ⟨fun hb ↦ by simpa using @hb false trivial,
    fun hb ↦ by simpa using @hb true trivial⟩ fun v _ ↦ ?_
  cases v <;> simp

/-! ### Negated neg-raising predicates ((57)–(65))

The neg-raising predicate (59) is `NegRaising.box`. Its negation (60) is true exactly where
the predicate holds of the negated complement (61), `NegRaising.posExt_negation`, which is
EVERY(NOT(_)), and so it is anti-additive ((62)–(64)),
`NegRaising.isAntiAdditive_posExt_negation`. -/

-- (61)
theorem posExt_negation_eq_every (R H : SetRel W W) (p : Set W) :
    Trivalent.posExt (negation R H p) = every R pᶜ :=
  posExt_negation R H p

-- (1)
theorem posExt_negation_subset (R H : SetRel W W) (p : Set W) :
    Trivalent.posExt (negation R H p) ⊆ R.core pᶜ :=
  (posExt_negation R H p).trans_subset Set.inter_subset_right

open Classical in
/-- A neg-raising predicate under stressed negation, where the assertion operator cancels the
excluded middle (fn. 7 (ii)). -/
noncomputable def notNRStressed (R : SetRel W W) (p : Set W) : W → Trivalent := fun w ↦
  (Trivalent.ofProp (box R R (fun u ↦ Trivalent.ofProp (u ∈ p)) w = .true))ᶜ

-- §2.1.3
theorem posExt_notNRStressed (R : SetRel W W) (p : Set W) :
    Trivalent.posExt (notNRStressed R p) = (R.core p)ᶜ := by
  ext w
  simp only [notNRStressed, box, Trivalent.mem_posExt, Trivalent.compl_eq_true_iff,
    Trivalent.ofProp_eq_false_iff, Trivalent.condEvent_eq_true_iff,
    Trivalent.ofProp_eq_true_iff, ne_eq, Trivalent.ofProp_ne_undefined, not_false_eq_true, Box,
    implies_true, true_and, not_and, Set.mem_compl_iff, mem_core]
  exact ⟨fun h hall ↦ h (.inl hall) hall, fun h _ ↦ h⟩

/-- Negated *know*, a factive universal without neg-raising, built from the substrate's negated
factive. -/
noncomputable def notKnow (R : SetRel W W) (p : Set W) : W → Trivalent :=
  (TwoDim.negFactive (pure (· ∈ p) : TwoDim W (W → Prop)) (Box R)).toTrivalent

-- (58b)
theorem not_isAntiAdditive_posExt_notKnow :
    ¬ IsAntiAdditive fun p : Set (Fin 3) ↦ Trivalent.posExt (notKnow .univ p) := by
  rw [isAntiAdditive_iff_mem]
  intro h
  have := (h {0, 1} {0, 2} 0).2
  simp only [notKnow, Trivalent.mem_posExt, TwoDim.toTrivalent_eq_true_iff,
    TwoDim.negFactive_atIssue, TwoDim.negFactive_notAtIssue,
    TwoDim.pure_atIssue, TwoDim.pure_notAtIssue, Pi.top_apply, Prop.top_eq_true, true_and, Box,
    Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_union] at this
  revert this
  decide

/-! ### Negative quantifiers (§3.1) -/

open Classical in
/-- *No one thinks p* (83) has the excluded middle projecting universally from the scope of the
quantifier ([heim-1983]). -/
noncomputable def noOneNR {E : Type*} (O : Set E) (B : E → SetRel W W) (p : Set W) :
    W → Trivalent := fun w ↦
  (Trivalent.existsWeak fun x : O ↦ box (B x) (B x) (fun u ↦ Trivalent.ofProp (u ∈ p)) w)ᶜ

-- (87), (89)
theorem posExt_noOneNR {E : Type*} (O : Set E) (B : E → SetRel W W) (p : Set W) :
    Trivalent.posExt (noOneNR O B p) = ⋂ x ∈ O, every (B x) pᶜ := by
  ext w
  simp [noOneNR, box_eq_false_iff, Box]

-- (90)
theorem isAntiAdditive_posExt_noOneNR {E : Type*} (O : Set E) (B : E → SetRel W W) :
    IsAntiAdditive fun p ↦ Trivalent.posExt (noOneNR O B p) := by
  rw [show (fun p ↦ Trivalent.posExt (noOneNR O B p)) = fun p ↦ ⋂ x ∈ O, every (B x) pᶜ from
    funext (posExt_noOneNR O B)]
  exact isAntiAdditive_iInf fun _ ↦ isAntiAdditive_iInf fun _ ↦
    isAntiAdditive_every isAntiAdditive_compl

/-! ### Stacked neg-raising predicates (§3.2–3.3, Appendix 2) -/

open Classical in
/-- Negation over a neg-raising predicate over another. -/
noncomputable def notStack (R₁ H₁ R₂ H₂ : SetRel W W) (p : Set W) : W → Trivalent :=
  (box R₁ H₁ (box R₂ H₂ fun u ↦ Trivalent.ofProp (u ∈ p)))ᶜ

open Classical in
-- (107), (110), Appendix 2, (9), (13)
theorem posExt_notStack_self (R₁ R₂ H₂ : SetRel W W) (p : Set W) :
    Trivalent.posExt (notStack R₁ R₁ R₂ H₂ p) = every R₁ (every R₂ pᶜ) := by
  ext w
  have h u : box R₂ H₂ (fun u ↦ Trivalent.ofProp (u ∈ p)) u = .false ↔ u ∈ every R₂ pᶜ := by
    rw [← posExt_negation_eq_every R₂ H₂]
    simp [negation]
  simp only [notStack, Trivalent.mem_posExt, Pi.compl_apply, Trivalent.compl_eq_true_iff,
    box_self_eq_false_iff, h, mem_every, Box]

-- (95)
theorem posExt_notStack_self_subset (R₁ R₂ H₂ : SetRel W W) (p : Set W) :
    Trivalent.posExt (notStack R₁ R₁ R₂ H₂ p) ⊆ R₁.core (R₂.core pᶜ) :=
  (posExt_notStack_self R₁ R₂ H₂ p).trans_subset fun _ hw _ hu ↦ (hw.2 hu).2

-- (97a)
theorem isAntiAdditive_posExt_notStack_self (R₁ R₂ H₂ : SetRel W W) :
    IsAntiAdditive fun p ↦ Trivalent.posExt (notStack R₁ R₁ R₂ H₂ p) := by
  rw [show (fun p ↦ Trivalent.posExt (notStack R₁ R₁ R₂ H₂ p)) = every R₁ ∘ (every R₂ ∘ compl) from
    funext (posExt_notStack_self R₁ R₂ H₂)]
  exact isAntiAdditive_every (isAntiAdditive_every isAntiAdditive_compl)

-- (111), (113), Appendix 2, (3)
theorem posExt_notStack (R₁ H₁ R₂ : SetRel W W) (p : Set W) :
    Trivalent.posExt (notStack R₁ H₁ R₂ R₂ p) =
      H₁.core (R₂.core p ∪ R₂.core pᶜ) ∩ every R₁ (R₂.core p)ᶜ := by
  ext w
  simp only [notStack, Trivalent.mem_posExt, Pi.compl_apply, Trivalent.compl_eq_true_iff,
    box_eq_false_iff, Set.mem_inter_iff, mem_every, mem_core, Set.mem_union, Set.mem_compl_iff]
  simp only [ne_eq, box, Trivalent.condEvent_eq_undefined_iff, Trivalent.condEvent_eq_true_iff,
    Trivalent.ofProp_eq_true_iff, Trivalent.ofProp_ne_undefined, not_false_eq_true, Box,
    implies_true, true_and, not_not, not_and]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun u _ ↦
    ⟨fun h hall ↦ h (.inl hall) hall, fun h _ ↦ h⟩

/-! The model (7) of Appendix 2 for *c doesn't want a to believe that p*. The evaluation world is
`0`, c's desire worlds are `1` and `2`, a believes `3` and `4` possible at `1` and `5` and `6` at
`2`, and `p` holds at `3` and `5`, `q` at `4` and `6`. World `7` is a belief world of c at which a
is opinionated. -/

/-- c's desire alternatives (7a). -/
abbrev desC : SetRel (Fin 8) (Fin 8) := {x | x.1 = 0 ∧ (x.2 = 1 ∨ x.2 = 2)}

/-- c's belief alternatives. -/
abbrev belC : SetRel (Fin 8) (Fin 8) := {x | x.1 = 0 ∧ x.2 = 7}

/-- a's belief alternatives (7b). -/
abbrev belA : SetRel (Fin 8) (Fin 8) :=
  {x | (x.1 = 1 ∧ (x.2 = 3 ∨ x.2 = 4)) ∨ (x.1 = 2 ∧ (x.2 = 5 ∨ x.2 = 6)) ∨ (x.1 = 7 ∧ x.2 = 7)}

-- In each of c's desire worlds a has a belief world outside the proposition.
private theorem mem_posExt_notStack_iff (s : Set (Fin 8)) :
    0 ∈ Trivalent.posExt (notStack desC belC belA belA s) ↔
      (3 ∉ s ∨ 4 ∉ s) ∧ (5 ∉ s ∨ 6 ∉ s) := by
  rw [posExt_notStack]
  simp [em]

-- (96), (114)
theorem not_posExt_notStack_subset :
    ¬ Trivalent.posExt (notStack desC belC belA belA {3, 5}) ⊆ desC.core (belA.core {3, 5}ᶜ) :=
  fun h ↦ h ((mem_posExt_notStack_iff _).2 ⟨.inr (by simp), .inr (by simp)⟩)
    (show (0, 1) ∈ desC from ⟨rfl, .inl rfl⟩) (show (1, 3) ∈ belA from .inl ⟨rfl, .inl rfl⟩)
    (Set.mem_insert 3 _)

/-- *Not want think* is not anti-additive ((97b), Appendix 2 (6)–(8)): c wants a not to believe
`p` and not to believe `q`, while a believes `p ∨ q` in each of c's desire worlds. -/
theorem not_isAntiAdditive_posExt_notStack :
    ¬ IsAntiAdditive fun p ↦ Trivalent.posExt (notStack desC belC belA belA p) := by
  rw [isAntiAdditive_iff_mem]
  intro h
  have := (mem_posExt_notStack_iff _).1 ((h {3, 5} {4, 6} 0).2
    ⟨(mem_posExt_notStack_iff _).2 ⟨.inr (by simp), .inr (by simp)⟩,
      (mem_posExt_notStack_iff _).2 ⟨.inl (by simp), .inl (by simp)⟩⟩)
  simp at this

/-! ### The environments as licensers

Each environment of the paper is a licenser of the library's licensing theory. A presupposing
licenser holds a strength of negation on its truth sets, which is the standard entailment that
Appendix 1 argues for. -/

/-- The beliefs of each of a nonempty set of people. -/
structure People where
  /-- The worlds. -/
  W : Type
  /-- The individuals. -/
  E : Type
  /-- The people. -/
  O : Set E
  /-- The belief alternatives of each individual. -/
  B : E → SetRel W W
  nonempty : O.Nonempty

/-- Two stacked neg-raising predicates, of which one is doxastic and the other projects the
presupposition of its complement into its subject's beliefs. -/
structure Stack where
  /-- The worlds. -/
  W : Type
  /-- The modal base of the higher predicate. -/
  upper : SetRel W W
  /-- The modal base of the lower predicate. -/
  lower : SetRel W W
  /-- The belief alternatives of the subject of the predicate that is not doxastic. -/
  beliefs : SetRel W W

/-- The environments in which the paper places a strict NPI. -/
inductive Environment
  /-- A context that the library names: sentential negation (12b), a negated neg-raising predicate
  as in *doesn't think* (15), *only DP* (123), an adversative (126), a conditional antecedent
  (127), the relative clause of a superlative (132). -/
  | named (c : LicensingContext)
  /-- No licenser, (12a), (13a). -/
  | positive
  /-- NOT(SOME(_)), as in *not a single*, *not allowed*, *can't* and *not possible*. -/
  | notSome
  /-- NOT(EVERY(_)), as in *not every*, *didn't claim*, *not required* and *not certain*. -/
  | notEvery
  /-- A neg-raising predicate under stressed negation, fn. 7 (ii). -/
  | notThinkStressed
  /-- Negated *know*, (58b). -/
  | notKnow
  /-- A negative quantifier over a neg-raising predicate, (83). -/
  | noOneThinks
  /-- A negated doxastic neg-raising predicate over another, as in *don't believe … wanted*. -/
  | notThinkWant
  /-- A negated bouletic or deontic neg-raising predicate over a doxastic one, as in *don't want …
  believe* and *shouldn't think*. -/
  | notWantThink
  deriving DecidableEq, Repr

open LicensingContext in
/-- The licenser of an environment. NOT(SOME(_)) is the operator the library gives *nobody* and
NOT(EVERY(_)) the one it gives *doubt*, over individuals or accessible worlds alike (48). -/
noncomputable def Environment.licenser : Environment → Licenser
  | .named c => c.licenser
  | .positive => .ofOperator (id : Prop → Prop)
  | .notSome => nobody.licenser
  | .notEvery => doubtVerb.licenser
  | .notThinkStressed => .strawson ⟨Frame, fun p ↦ Set p.W, fun p ↦ p.W, fun p ↦ notNRStressed p.R⟩
  | .notKnow => .strawson ⟨Frame, fun p ↦ Set p.W, fun p ↦ p.W, fun p ↦ Gajewski2007.notKnow p.R⟩
  | .noOneThinks => .strawson ⟨People, fun p ↦ Set p.W, fun p ↦ p.W, fun p ↦ noOneNR p.O p.B⟩
  | .notThinkWant => .strawson
      ⟨Stack, fun p ↦ Set p.W, fun p ↦ p.W, fun p ↦ notStack p.upper p.upper p.lower p.beliefs⟩
  | .notWantThink => .strawson
      ⟨Stack, fun p ↦ Set p.W, fun p ↦ p.W, fun p ↦ notStack p.upper p.beliefs p.lower p.lower⟩

theorem carries_noOneThinks : Environment.noOneThinks.licenser.Carries .antiAdditive :=
  Licenser.carries_strawson_antiAdditive (fun p ↦ isAntiAdditive_posExt_noOneNR p.O p.B)
    (fun p ↦ by
      obtain ⟨x, hx⟩ := p.nonempty
      exact Set.eq_empty_of_forall_notMem fun w hw ↦ by
        rw [posExt_noOneNR] at hw
        simpa using Set.mem_iInter₂.1 hw x hx)
    ⟨⟨Unit, Unit, .univ, fun _ ↦ .univ, ⟨(), trivial⟩⟩,
      not_isStrawsonUE (w := ()) (Set.empty_subset Set.univ)
        (by simp [noOneNR, box_eq_false_iff, Box]) (by simp [noOneNR, box, Box])⟩

theorem carries_notThinkWant : Environment.notThinkWant.licenser.Carries .antiAdditive :=
  Licenser.carries_strawson_antiAdditive
    (fun p ↦ isAntiAdditive_posExt_notStack_self p.upper p.lower p.beliefs)
    (fun p ↦ by simp [posExt_notStack_self])
    ⟨⟨Unit, .univ, .univ, .univ⟩, not_isStrawsonUE (w := ()) (Set.empty_subset Set.univ)
      (by simp [notStack, box, Box]) (by simp [notStack, box, Box])⟩

theorem not_carries_notThinkStressed :
    ¬ Environment.notThinkStressed.licenser.Carries .antiAdditive :=
  Licenser.not_carries_strawson_antiAdditive ⟨⟨Bool, .univ⟩, by
    simpa only [posExt_notNRStressed] using not_isAntiAdditive_compl_core⟩

theorem not_carries_notKnow : ¬ Environment.notKnow.licenser.Carries .antiAdditive :=
  Licenser.not_carries_strawson_antiAdditive ⟨⟨Fin 3, .univ⟩, not_isAntiAdditive_posExt_notKnow⟩

theorem not_carries_notWantThink : ¬ Environment.notWantThink.licenser.Carries .antiAdditive :=
  Licenser.not_carries_strawson_antiAdditive
    ⟨⟨Fin 8, desC, belA, belC⟩, not_isAntiAdditive_posExt_notStack⟩

instance (e : Environment) : Decidable (e.licenser.Carries .antiAdditive) :=
  match e with
  | .named c => inferInstanceAs (Decidable (c.licenser.Carries .antiAdditive))
  | .positive => isFalse fun h ↦ h.weak.2 fun _ ↦ monotone_id
  | .notSome => inferInstanceAs (Decidable (LicensingContext.nobody.licenser.Carries _))
  | .notEvery => inferInstanceAs (Decidable (LicensingContext.doubtVerb.licenser.Carries _))
  | .notThinkStressed => isFalse not_carries_notThinkStressed
  | .notKnow => isFalse not_carries_notKnow
  | .noOneThinks => isTrue carries_noOneThinks
  | .notThinkWant => isTrue carries_notThinkWant
  | .notWantThink => isFalse not_carries_notWantThink

/-! ### The paper's judgments -/

open Examples

/-- A link from an example to the lexical entry of its strict NPI and to the environment in which
the item stands. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The environment of the item. -/
  environment : Environment

open English.PolarityItems in
/-- The links of the examples. Stress cancels neg-raising in fn. 7 (ii), *claim* and *know* do not
neg-raise, and in (98)–(99) *should* and *ought* take the place of *want*. -/
def links : List (Datum × Link) :=
  [(ex_12a, ⟨until_, .positive⟩), (ex_12b, ⟨until_, .named .negation⟩),
    (ex_13a, ⟨inYears, .positive⟩), (ex_13b, ⟨inYears, .named .negation⟩),
    (ex_14a, ⟨until_, .notEvery⟩), (ex_14b, ⟨inYears, .notEvery⟩),
    (ex_15a, ⟨until_, .named .superordinateNegation⟩),
    (ex_15b, ⟨inYears, .named .superordinateNegation⟩),
    (ex_54a, ⟨inYears, .notSome⟩), (ex_54b, ⟨inYears, .notEvery⟩),
    (ex_57, ⟨until_, .named .superordinateNegation⟩),
    (ex_58a, ⟨inYears, .named .superordinateNegation⟩), (ex_58b, ⟨inYears, .notKnow⟩),
    (ex_68a, ⟨until_, .notEvery⟩), (ex_68b, ⟨until_, .notSome⟩),
    (ex_69a, ⟨inYears, .notEvery⟩), (ex_69b, ⟨inYears, .notSome⟩),
    (ex_71a, ⟨inYears, .notSome⟩), (ex_71b, ⟨inYears, .notSome⟩),
    (ex_72a, ⟨inYears, .notEvery⟩), (ex_72b, ⟨inYears, .notEvery⟩),
    (ex_73, ⟨inYears, .notEvery⟩), (ex_74, ⟨inYears, .notSome⟩),
    (ex_83, ⟨until_, .noOneThinks⟩),
    (ex_97a, ⟨until_, .notThinkWant⟩), (ex_97b, ⟨until_, .notWantThink⟩),
    (ex_98a, ⟨until_, .notThinkWant⟩), (ex_98b, ⟨until_, .notWantThink⟩),
    (ex_99a, ⟨until_, .notThinkWant⟩), (ex_99b, ⟨until_, .notWantThink⟩),
    (ex_123a, ⟨until_, .named .onlyFocus⟩), (ex_123b, ⟨inYears, .named .onlyFocus⟩),
    (ex_123c, ⟨either, .named .onlyFocus⟩),
    (ex_126a, ⟨until_, .named .adversative⟩), (ex_126b, ⟨inYears, .named .adversative⟩),
    (ex_127a, ⟨until_, .named .conditionalAntecedent⟩),
    (ex_127b, ⟨inYears, .named .conditionalAntecedent⟩),
    (ex_132a, ⟨inYears, .named .superlative⟩), (ex_132b, ⟨until_, .named .superlative⟩),
    (fn7ii, ⟨inYears, .notThinkStressed⟩)]

-- Every example is linked, and the words of each link's item occur in its example, so a link to
-- the wrong item fails.
theorem links_attested :
    links.map (·.1) = Examples.all ∧ ∀ p ∈ links, ∀ w ∈ Datum.wordsOf p.2.item.form,
      w ∈ Datum.wordsOf p.1.primaryText := by
  decide +kernel

private theorem links_strict :
    ∀ p ∈ links, p.2.item.licensor = some .antiAdditive ∧ p.2.item.antiLicensor = none ∧
      ¬ p.2.item.IsFCI := by
  decide +kernel

private theorem links_carries :
    ∀ p ∈ links, p.2.environment ≠ .named .superlative → p.1 ≠ ex_74 →
      (p.1.judgment = .acceptable ↔ p.2.environment.licenser.Carries .antiAdditive) := by
  decide +kernel

/-- The licensing theory admits the strict NPI of each example in its environment exactly when the
paper judges the example acceptable (55), the superlatives of (132) and the finite clause boundary
of (74) aside. -/
theorem judgments_predicted :
    ∀ p ∈ links, p.2.environment ≠ .named .superlative → p.1 ≠ ex_74 →
      (p.1.judgment = .acceptable ↔ p.2.environment.licenser.Admits p.2.item) :=
  fun p hp hs h74 ↦
    have ⟨hl, ha, hf⟩ := links_strict p hp
    (links_carries p hp hs h74).trans (Licenser.admits_iff_carries hl (by decide) ha hf).symm

/-- Strict NPIs are acceptable in superlative relative clauses, which are Strawson downward
entailing and not anti-additive, the exception the paper leaves open (132). -/
theorem superlative_exception :
    ∀ p ∈ links, p.2.environment = .named .superlative →
      p.1.judgment = .acceptable ∧ LicensingContext.superlative.licenser.IsStrawsonDE ∧
        ¬ p.2.environment.licenser.Carries .antiAdditive := by
  have h : ∀ p ∈ links, p.2.environment = .named .superlative →
      p.1.judgment = .acceptable ∧ ¬ p.2.environment.licenser.Carries .antiAdditive := by
    decide +kernel
  exact fun p hp he ↦ ⟨(h p hp he).1, LicensingContext.isStrawsonDE_superlative, (h p hp he).2⟩

-- (74), (73)
theorem finite_boundary :
    ex_74.judgment = .questionable ∧ Environment.notSome.licenser.Carries .antiAdditive := by
  decide +kernel

end Gajewski2007
