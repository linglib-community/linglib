module

public import Linglib.Data.Examples.CoppockWechsler2018
public import Linglib.Discourse.Commitment.Table
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Reference.Kaplan
public import Studies.Pearson2015

/-!
# Coppock & Wechsler (2018): The Proper Treatment of Egophoricity in Kathmandu Newari

This file formalizes Coppock and Wechsler's account of egophoric marking in Kathmandu Newari.
Newari verbs carry no person agreement. A special *egophoric* form appears in statements about
the speaker, in questions about the addressee, and in reports where the reported speaker was
knowingly talking about herself. The plain form appears elsewhere.

A sentence is evaluated at a context, a world and an agent called the *perspectival center*, and
the egophoric suffix presupposes that the subject is the center (`ego`). Every context has an
*authority*, the speaker of a statement and the addressee of a question, and a speech act
proposes its meaning with the authority as center. When the subject is not the authority the
proposal is empty and the conversation cannot continue (`inCrisis_assert_ego`,
`inCrisis_ask_ego`), which gives *I* in statements and *you* in questions. A report is true only
if the reported speaker took the subject to be herself (`says_ego_iff`). A simpler account, on
which the suffix presupposes that the subject is the authority, agrees on main clauses and
fails when Syam comments on a photograph of himself that he does not recognize (`lampshade`).

## Implementation notes

* The Table records the public side of the paper's discourse model, the common ground and its
  projections. The centered meaning is the argument of `assert`, `ask` and `Says`.
* Expressions of the paper's logic are given by their meanings rather than as syntax, and time
  is ignored as in the paper.

## TODO

The paper marks the second-person question with the plain form as unacceptable. The account
derives where the egophoric form is excluded, not where it is required.

## References

* [coppock-wechsler-2018]
* [farkas-bruce-2010]
* [pearson-2015]
-/

@[expose] public section

namespace CoppockWechsler2018

open Commitment Question Filter
open Pearson2015 (Centered SayDeSe)

variable {W E P T : Type*}

/-! ### Contexts, terms and meanings -/

/-- A context of utterance together with its authority, the person who vouches for what is said
in it. -/
structure Context (W E P T : Type*) extends Reference.Context W E P T where
  /-- The epistemic authority of the context. -/
  authority : E

/-- A context is declarative when its authority is the speaker. -/
def Context.IsDeclarative (c : Context W E P T) : Prop := c.authority = c.agent

/-- A context is interrogative when its authority is the addressee. -/
def Context.IsInterrogative (c : Context W E P T) : Prop := c.authority = c.addressee

/-- A term denotes an individual, which may depend on the context and on the perspectival
center. -/
abbrev Term (W E P T : Type*) := Context W E P T → E → E

/-- The pronoun *I* denotes the speaker of the context. -/
def I : Term W E P T := fun c _ ↦ c.agent

/-- The pronoun *you* denotes the addressee of the context. -/
def you : Term W E P T := fun c _ ↦ c.addressee

/-- The term `auth` denotes the authority of the context. -/
def auth : Term W E P T := fun c _ ↦ c.authority

/-- The term `self` denotes the perspectival center. -/
def self : Term W E P T := fun _ a ↦ a

/-- A name denotes the same individual at every context and center. -/
def name (x : E) : Term W E P T := fun _ _ ↦ x

/-- A centered proposition is true, false or undefined at a world together with a center. It is
undefined where its presupposition fails. -/
abbrev CenteredProp (W E : Type*) := Centered W E → SignType

variable (V : E → W → Prop) (t : Term W E P T) (c : Context W E P T)

open Classical in
/-- The meaning of a clause whose verb carries the egophoric suffix. It asserts that the subject
has the property `V` and presupposes that the subject is the center. -/
noncomputable def ego : CenteredProp W E :=
  {p | t c p.2 = p.2}.indicator fun p ↦ SignType.ofProp (V (t c p.2) p.1)

open Classical in
/-- The meaning of a clause whose verb is in the plain form. It asserts that the subject has the
property `V` and presupposes nothing. -/
noncomputable def plain : CenteredProp W E := fun p ↦ SignType.ofProp (V (t c p.2) p.1)

open Classical in
/-- The meaning of an egophoric clause on the authority-indexical account, which presupposes
that the subject is the authority of the context rather than the center. -/
noncomputable def egoAuth : CenteredProp W E :=
  {p | t c p.2 = c.authority}.indicator fun p ↦ SignType.ofProp (V (t c p.2) p.1)

/-- Filling in `x` as the center of a centered proposition gives an ordinary proposition, the
set of worlds where it is defined and true of `x`. -/
def uncenter (φ : CenteredProp W E) (x : E) : Set W := {w | φ (w, x) = 1}

variable {V t c} {x : E}

@[simp] theorem ego_eq_one_iff {p : Centered W E} :
    ego V t c p = 1 ↔ t c p.2 = p.2 ∧ V (t c p.2) p.1 := by
  simp [ego]

@[simp] theorem plain_eq_one_iff {p : Centered W E} : plain V t c p = 1 ↔ V (t c p.2) p.1 := by
  simp [plain]

theorem uncenter_ego_of_eq (h : t c x = x) : uncenter (ego V t c) x = {w | V x w} := by
  ext w; simp [uncenter, h]

theorem uncenter_ego_of_ne (h : t c x ≠ x) : uncenter (ego V t c) x = ∅ := by
  ext w; simp [uncenter, h]

theorem uncenter_neg_ego_of_eq (h : t c x = x) :
    uncenter (-ego V t c) x = {w | V x w}ᶜ := by
  ext w; simp [uncenter, ego, h]

theorem uncenter_neg_ego_of_ne (h : t c x ≠ x) : uncenter (-ego V t c) x = ∅ := by
  ext w; simp [uncenter, ego, h]

/-- In a main clause the two accounts propose the same thing for the common ground. -/
theorem uncenter_egoAuth :
    uncenter (egoAuth V t c) c.authority = uncenter (ego V t c) c.authority := rfl

/-! ### Moves on the Table -/

/-- Asserting `φ` commits the authority of the context and proposes `φ`, with the authority as
center, for the common ground. -/
def assert (K : Table E W) (c : Context W E P T) (φ : CenteredProp W E) : Table E W :=
  K.assert c.authority (uncenter φ c.authority)

/-- Asking whether `φ` puts its two answers on the Table, each with the authority as center.
Both answers keep the presupposition of `φ`. -/
def ask (K : Table E W) (c : Context W E P T) (φ : CenteredProp W E) : Table E W :=
  K.push (ofSet (uncenter φ c.authority) ⊔ ofSet (uncenter (-φ) c.authority))

variable {K : Table E W}

/-- If the only answer to the issue on top of the Table is the empty proposition, the
conversation has no consistent continuation. -/
theorem inCrisis_push_ofSet_empty : (K.push (ofSet (∅ : Set W))).InCrisis := by
  refine (Table.inCrisis_iff _).2 fun f hf ↦ ?_
  obtain ⟨⟨g, -, q, hq, rfl⟩, hne⟩ := hf
  rw [alt_ofSet, Set.mem_singleton_iff] at hq
  simp [hq] at hne

/-- Asserting an egophoric clause whose subject is not the authority leaves the conversation
with no consistent continuation. -/
theorem inCrisis_assert_ego (h : t c c.authority ≠ c.authority) :
    (assert K c (ego V t c)).InCrisis := by
  rw [assert, uncenter_ego_of_ne h]
  exact inCrisis_push_ofSet_empty (K := K.commit c.authority ∅)

/-- Asking an egophoric question whose subject is not the authority leaves the conversation
with no consistent continuation. -/
theorem inCrisis_ask_ego (h : t c c.authority ≠ c.authority) :
    (ask K c (ego V t c)).InCrisis := by
  rw [ask, uncenter_ego_of_ne h, uncenter_neg_ego_of_ne h, sup_idem]
  exact inCrisis_push_ofSet_empty

/-- When the subject is the authority, asserting an egophoric clause is an ordinary assertion
that the authority has the property. -/
theorem assert_ego_of_eq (h : t c c.authority = c.authority) :
    assert K c (ego V t c) = K.assert c.authority {w | V c.authority w} := by
  rw [assert, uncenter_ego_of_eq h]

/-- When the subject is the authority, asking an egophoric question is an ordinary polar
question about whether the authority has the property. -/
theorem ask_ego_of_eq (h : t c c.authority = c.authority) :
    ask K c (ego V t c) = K.polarQuestion {w | V c.authority w} := by
  rw [ask, uncenter_ego_of_eq h, uncenter_neg_ego_of_eq h]; rfl

/-- When the subject is the authority, an egophoric assertion can be continued consistently,
provided the Table is empty and the common ground allows that the authority has the property. -/
theorem not_inCrisis_assert_ego (h : t c c.authority = c.authority) (hK : K.IsStable)
    (hV : K.commonGround ⊓ 𝓟 {w | V c.authority w} ≠ ⊥) :
    ¬ (assert K c (ego V t c)).InCrisis := by
  rw [assert_ego_of_eq h, Table.inCrisis_iff, Table.projectedSet_assert,
    Table.projectedSet_of_isStable hK, Table.project_singleton_ofSet hV]
  exact fun hf ↦ hV (hf _ rfl)

/-- When the subject is the authority, an egophoric question can be continued consistently,
provided the Table is empty and the common ground leaves open whether the authority has the
property. -/
theorem not_inCrisis_ask_ego (h : t c c.authority = c.authority) (hK : K.IsStable)
    (hV : K.commonGround ⊓ 𝓟 {w | V c.authority w} ≠ ⊥)
    (hV' : K.commonGround ⊓ 𝓟 {w | V c.authority w}ᶜ ≠ ⊥) :
    ¬ (ask K c (ego V t c)).InCrisis := by
  rw [ask_ego_of_eq h, Table.inCrisis_iff, Table.projectedSet_polarQuestion,
    Table.projectedSet_of_isStable hK, Table.project_singleton_polar hV hV']
  exact fun hf ↦ hV (hf _ (Set.mem_insert _ _))

/-! ### Which subjects the egophoric form allows -/

/-- A statement with *you* as the subject of an egophoric verb has no consistent
continuation. -/
theorem inCrisis_assert_ego_you (hne : c.agent ≠ c.addressee) (hc : c.IsDeclarative) :
    (assert K c (ego V you c)).InCrisis :=
  inCrisis_assert_ego (t := you) fun h ↦ hne (h.trans hc).symm

/-- A question with *I* as the subject of an egophoric verb has no consistent continuation. -/
theorem inCrisis_ask_ego_I (hne : c.agent ≠ c.addressee) (hc : c.IsInterrogative) :
    (ask K c (ego V I c)).InCrisis :=
  inCrisis_ask_ego (t := I) fun h ↦ hne (h.trans hc)

/-- When an evidential makes someone other than the speaker the authority, a statement with *I*
as the subject of an egophoric verb has no consistent continuation. -/
theorem inCrisis_assert_ego_I_of_source (hs : c.agent ≠ c.authority) :
    (assert K c (ego V I c)).InCrisis :=
  inCrisis_assert_ego (t := I) hs

/-- If an egophoric assertion can be continued consistently, its subject is the authority. -/
theorem eq_authority_of_not_inCrisis_assert (h : ¬ (assert K c (ego V t c)).InCrisis) :
    t c c.authority = c.authority :=
  of_not_not fun hne ↦ h (inCrisis_assert_ego hne)

/-- If an egophoric question can be continued consistently, its subject is the authority. -/
theorem eq_authority_of_not_inCrisis_ask (h : ¬ (ask K c (ego V t c)).InCrisis) :
    t c c.authority = c.authority :=
  of_not_not fun hne ↦ h (inCrisis_ask_ego hne)

/-! ### The paper's examples -/

section Rows


/-- The subject of an example is *I* or *you*, according to the person of its pronoun. -/
def subject? (r : Datum) : Option (Term W E P T) :=
  match r.feature? "subject" with
  | some "1" => some I
  | some "2" => some you
  | _ => none

/-- The context of an example has the speaker as its authority if the example is a statement
and the addressee if it is a question. -/
def context? (r : Datum) (c₀ : Reference.Context W E P T) :
    Option (Context W E P T) :=
  match r.feature? "clause" with
  | some "declarative" => some ⟨c₀, c₀.agent⟩
  | some "interrogative" => some ⟨c₀, c₀.addressee⟩
  | _ => none

/-- Among the paper's examples with an egophoric verb, the acceptable ones are exactly those
whose subject is the authority. -/
theorem ego_acceptable_iff (c₀ : Reference.Context W E P T) (hne : c₀.agent ≠ c₀.addressee) :
    ∀ r ∈ Examples.all, r.feature? "marking" = some "ego" →
      ∃ t ∈ subject? r, ∃ c ∈ context? r c₀,
        (r.judgment = .acceptable ↔ t c c.authority = c.authority) := by
  intro r hr hm
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨I, rfl, _, rfl, by simp [I, Examples.ex_27]⟩
  · exact ⟨you, rfl, _, rfl, by simp [you, Examples.ex_28, hne.symm]⟩
  · exact ⟨I, rfl, _, rfl, by simp [I, Examples.ex_34a, hne]⟩
  · exact absurd hm (by decide)
  · exact ⟨you, rfl, _, rfl, by simp [you, Examples.ex_35a]⟩
  · exact absurd hm (by decide)

end Rows

/-! ### Speech reports -/

/-- `x` says `φ` in `w` when `φ` is defined and true at every world and center compatible with
what `x` says in `w`. -/
def Says (R : Centered W E → Centered W E → Prop) (x : E) (φ : CenteredProp W E) (w : W) :
    Prop :=
  ∀ p, R (w, x) p → φ p = 1

open Classical in
/-- The meaning of *`x` says that `φ`*, which is the same at every center. -/
noncomputable def report (R : Centered W E → Centered W E → Prop) (x : E) (φ : CenteredProp W E) :
    CenteredProp W E :=
  fun p ↦ SignType.ofProp (Says R x φ p.1)

variable {R : Centered W E → Centered W E → Prop} {φ : CenteredProp W E} {w : W} {y z : E}

@[simp] theorem report_eq_one_iff {p : Centered W E} : report R x φ p = 1 ↔ Says R x φ p.1 := by
  simp [report]

/-- `Says` is `Pearson2015.SayDeSe` over the alternatives of the say relation. -/
theorem says_iff_sayDeSe : Says R x φ w ↔ SayDeSe {p | R (w, x) p} fun a w' ↦ φ (w', a) = 1 :=
  Iff.rfl

/-- An egophoric report is true exactly when the reported speaker takes the subject to be
herself and ascribes the property to herself. -/
theorem says_ego_iff :
    Says R x (ego V t c) w ↔
      (∀ p, R (w, x) p → t c p.2 = p.2) ∧ Says R x (ego V self c) w := by
  simp only [Says, ego_eq_one_iff, self, true_and]
  exact ⟨fun h ↦ ⟨fun p hp ↦ (h p hp).1, fun p hp ↦ (h p hp).1 ▸ (h p hp).2⟩,
    fun h p hp ↦ ⟨h.1 p hp, (h.1 p hp).symm ▸ h.2 p hp⟩⟩

/-- If an egophoric report is true, so is the corresponding plain report. -/
theorem says_plain_of_says_ego (h : Says R x (ego V t c) w) : Says R x (plain V t c) w :=
  fun p hp ↦ plain_eq_one_iff.2 (ego_eq_one_iff.1 (h p hp)).2

/-- A speaker is self-aware when she says something at every world and takes herself to be who
she is. -/
structure SelfAware (R : Centered W E → Centered W E → Prop) (x : E) : Prop where
  serial : ∀ w, ∃ p, R (w, x) p
  center : ∀ w p, R (w, x) p → p.2 = x

/-- When one report is embedded in another, the subject of the egophoric verb is the speaker of
the inner report, whoever the outer speaker is. -/
theorem eq_of_says_report_ego (hy : ∀ w, ∃ p, R (w, y) p) (hx : SelfAware R x)
    (h : Says R y (report R x (ego V (name z) c)) w) : z = x := by
  obtain ⟨p, hp⟩ := hy w
  obtain ⟨q, hq⟩ := hx.serial p.1
  exact (ego_eq_one_iff.1 (report_eq_one_iff.1 (h p hp) q hq)).1.trans (hx.center _ _ hq)

/-! ### The authority-indexical account -/

/-- On the authority-indexical account a report shifts the context so that the reported speaker
becomes the authority. -/
def authorityShift (x : E) : Function.End (Context W E P T) := fun c ↦ { c with authority := x }

/-- The shift changes the context, so evaluating a character at the shifted context is a monster
in Kaplan's sense. -/
theorem isMonster_authorityShift [Nonempty W] (h : c.authority ≠ x) :
    Reference.IsMonster (Reference.shift (authorityShift (W := W) (P := P) (T := T) x) :
      Reference.Character (Context W E P T) W Prop → _) :=
  (Reference.isMonster_shift_iff _).2 <|
    (Reference.ne_one_iff_exists_smul_ne _).2 ⟨c, fun e ↦ h (congrArg Context.authority e).symm⟩

/-- On the authority-indexical account a shifted report about a named individual is true exactly
when the individual is the reported speaker and the plain report is true. -/
theorem says_egoAuth_name_iff (hR : ∃ p, R (w, x) p) :
    Says R x (egoAuth V (name z) (authorityShift x c)) w ↔
      z = x ∧ Says R x (plain V (name z) c) w := by
  obtain ⟨p₀, hp₀⟩ := hR
  simp only [Says, egoAuth, plain_eq_one_iff, name, authorityShift,
    Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq, SignType.ofProp_eq_one_iff]
  exact ⟨fun h ↦ ⟨(h p₀ hp₀).1, fun p hp ↦ (h p hp).2⟩, fun h p hp ↦ ⟨h.1, h.2 p hp⟩⟩

/-! ### The unrecognized photograph

Syam points at a photograph of a man with a lampshade on his head and says *that guy drank too
much*. He does not realize that the man is himself. -/

section Lampshade

/-- The people of the scenario are Syam and the man Syam takes himself to be. -/
inductive Person | syam | other
  deriving DecidableEq

/-- The worlds of the scenario are the actual world and the world as Syam describes it. -/
inductive World | actual | said
  deriving DecidableEq

/-- Everything Syam says is compatible with his being someone other than the man in the
photograph. -/
def sayAlt : Centered World Person → Centered World Person → Prop :=
  fun p q ↦ p = (.actual, .syam) ∧ q = (.said, .other)

/-- The man in the photograph drank too much in the world Syam describes. -/
def drank : Person → World → Prop := fun x w ↦ x = .syam ∧ w = .said

variable (c : Context World Person Unit Unit)

/-- In the photograph scenario the plain report is true and the egophoric report is false. The
authority-indexical account makes the egophoric report true, because it checks only that the
subject is the reported speaker. -/
theorem lampshade :
    Says sayAlt .syam (plain drank (name .syam) c) .actual ∧
    ¬ Says sayAlt .syam (ego drank (name .syam) c) .actual ∧
    Says sayAlt .syam (egoAuth drank (name .syam) (authorityShift .syam c)) .actual := by
  refine ⟨?_, fun h ↦ ?_, ?_⟩
  · rintro p ⟨-, rfl⟩; simp [name, drank]
  · simpa [name] using h (.said, .other) ⟨rfl, rfl⟩
  · rintro p ⟨-, rfl⟩; simp [egoAuth, name, authorityShift, drank]

end Lampshade

end CoppockWechsler2018
