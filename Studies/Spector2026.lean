module

public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Data.Examples.Spector2026

/-!
# Spector (2026): Trivalence and transparency: a non-dynamic approach to anaphora

Spector interprets a first-order language statically at world–assignment pairs with partial
assignments. A predicate of an unvalued variable is undefined, the connectives follow the Middle
Kleene tables, and an existential is true only when the assignment already values its variable
with a witness. A free variable presupposes that it is valued, and a sentence is felicitous in a
context when Schlenker's symmetric Transparency holds at every occurrence of every free variable.
The full system evaluates at plural assignments, where a free variable presupposes that its value
is atomic; it restores covariation, captures quantificational subordination and the weak reading
of donkey sentences, and a strong-truth operator internalizes universal readings.

## Main statements

* `felicitous_forward_conj`, `felicitous_bathroom`, `not_felicitous_reverse_conj`: anaphora
  across conjunction and in bathroom sentences, and its sensitivity to order.
* `trueAtP_notExNotEx_iff`, `trueAtP_qs_iff`, `felicitousP_qs`: covariation and quantificational
  subordination in the full system.
* `trueAtP_donkey_iff`, `felicitousP_donkey`: the weak reading of donkey sentences, and
  Transparency for their pronoun.
* `stronglyTrueAt_ex_and_iff`: under Strong Truth, *there is a bathroom and it is upstairs* says
  that every bathroom is upstairs.

## Implementation notes

* One language serves both systems: `valued` is the paper's *U(x)* in the simplified system and
  *atomic(x)*, a single value `∃ d, G.value x = {d}`, in the full one, and the simplified
  evaluation leaves the universal and the strong-truth operator undefined.
* `Formula.occurrences` lists the free arguments of each atom with the presupposition the
  Transparency Condition tests there, *valued(x)* for each and *valued(x) ∧ valued(y)* when both
  arguments of a relation are free.
* The language has no individual constants, so Sue's owning and beating in (40) are one-place
  predicates.
* The functional variables of the appendix, which (35) and (61) need, are not formalized, nor is
  Stone disjunction, which the paper leaves open (fn. 15).

## References

* [spector-2026]
* [schlenker-2007]
* [schlenker-2008]
* [mandelkern-2022]
* [peters-1979]
* [beaver-krahmer-2001]
-/

@[expose] public section

namespace Spector2026

open SignType (meetMiddle joinMiddle ofProp)

/-! ### The language -/

/-- The language has one- and two-place predicates on variables, the valuedness predicate that
Transparency introduces, the connectives, and the quantifiers. -/
inductive Formula (P R : Type*) where
  | pred (p : P) (x : ℕ)
  | rel (r : R) (x y : ℕ)
  | valued (x : ℕ)
  | not (φ : Formula P R)
  | and (φ ψ : Formula P R)
  | or (φ ψ : Formula P R)
  | ex (x : ℕ) (φ : Formula P R)
  | all (x : ℕ) (φ : Formula P R)
  | strong (φ : Formula P R)

/-- A model gives the extensions of the predicates at each world. -/
structure Model (W D P R : Type*) where
  pred : P → W → Set D
  rel : R → W → Set (D × D)

/-- The variables an existential binds, for the Novelty Condition. -/
def Formula.binders {P R : Type*} : Formula P R → List ℕ
  | .pred _ _ | .rel _ _ _ | .valued _ => []
  | .not φ => φ.binders
  | .and φ ψ | .or φ ψ => φ.binders ++ ψ.binders
  | .ex x φ => x :: φ.binders
  | .all _ φ | .strong φ => φ.binders

/-- The Novelty Condition requires that no existential bind the same variable twice across a
discourse. -/
def Novel {P R : Type*} (S : List (Formula P R)) : Prop := (S.flatMap Formula.binders).Nodup

variable {W D P R : Type*} (M : Model W D P R)

/-! ### The simplified system: partial assignments -/

theorem conj_transparency_parametric (E presup φ : SignType) (hw : E = 1 → presup = 1) :
    meetMiddle E (meetMiddle presup φ) = meetMiddle E φ :=
  SignType.meetMiddle_congr_right fun h ↦ by rw [hw h, SignType.meetMiddle_one_left]

theorem disj_transparency_parametric (negE presup φ : SignType)
    (hw : negE = -1 → presup = 1) :
    joinMiddle negE (meetMiddle presup φ) = joinMiddle negE φ :=
  SignType.joinMiddle_congr_right fun h ↦ by rw [hw h, SignType.meetMiddle_one_left]

open Classical in
/-- Evaluation at a world and a partial assignment. A predicate of an unvalued variable is
undefined; the existential is true when its scope is, false when every value falsifies the
scope, undefined otherwise. The universal and the strong-truth operator belong to the full
system and are left undefined here. -/
noncomputable def eval : Formula P R → W → PartialAssign ℕ D → SignType
  | .pred p x, w, g =>
    match g x with
    | ⊥ => 0
    | (d : D) => ofProp (d ∈ M.pred p w)
  | .rel r x y, w, g =>
    match g x, g y with
    | (a : D), (b : D) => ofProp ((a, b) ∈ M.rel r w)
    | _, _ => 0
  | .valued x, _, g =>
    match g x with
    | ⊥ => (-1)
    | (_ : D) => 1
  | .not φ, w, g => -eval φ w g
  | .and φ ψ, w, g => meetMiddle (eval φ w g) (eval ψ w g)
  | .or φ ψ, w, g => joinMiddle (eval φ w g) (eval ψ w g)
  | .ex x φ, w, g =>
    if eval φ w g = 1 then 1
    else if ∀ a, eval φ w (g.update x a) = -1 then -1
    else 0
  | .all _ _, _, _ | .strong _, _, _ => 0

/-- A sentence is true at a world when some assignment makes it true. -/
def TrueAt (φ : Formula P R) (w : W) : Prop := ∃ g : PartialAssign ℕ D, eval M φ w g = 1

variable {M}

theorem eval_pred_of_eq_bot {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} (h : g x = ⊥) :
    eval M (.pred p x) w g = 0 := by
  simp [eval, h]

open Classical in
theorem eval_pred_of_eq_coe {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} {d : D}
    (h : g x = ↑d) : eval M (.pred p x) w g = ofProp (d ∈ M.pred p w) := by
  simp [eval, h]

theorem eval_pred_eq_true_iff {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} :
    eval M (.pred p x) w g = 1 ↔ ∃ d : D, g x = ↑d ∧ d ∈ M.pred p w := by
  cases h : g x with
  | bot => simp [eval_pred_of_eq_bot h]
  | coe d => simp [eval_pred_of_eq_coe h]

theorem eval_pred_eq_false_iff {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D} :
    eval M (.pred p x) w g = -1 ↔ ∃ d : D, g x = ↑d ∧ d ∉ M.pred p w := by
  cases h : g x with
  | bot => simp [eval_pred_of_eq_bot h]
  | coe d => simp [eval_pred_of_eq_coe h]

theorem eval_valued_of_ne_bot {x : ℕ} {w : W} {g : PartialAssign ℕ D} (h : g x ≠ ⊥) :
    eval M (.valued x) w g = 1 := by
  obtain ⟨d, hd⟩ := Flat.ne_bot_iff_exists.1 h
  simp [eval, hd]

theorem eval_valued_of_eq_bot {x : ℕ} {w : W} {g : PartialAssign ℕ D} (h : g x = ⊥) :
    eval M (.valued x) w g = -1 := by
  simp [eval, h]

@[simp] theorem eval_valued_bot (x : ℕ) (w : W) :
    eval M (.valued x) w (⊥ : PartialAssign ℕ D) = -1 := rfl

theorem eval_not {φ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.not φ) w g = -eval M φ w g := rfl

theorem eval_and {φ ψ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.and φ ψ) w g = meetMiddle (eval M φ w g) (eval M ψ w g) := rfl

theorem eval_or {φ ψ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.or φ ψ) w g = joinMiddle (eval M φ w g) (eval M ψ w g) := rfl

theorem eval_ex_eq_true_iff {x : ℕ} {φ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.ex x φ) w g = 1 ↔ eval M φ w g = 1 := by
  simp only [eval]
  split_ifs with h h' <;> simp [h]

theorem eval_ex_eq_false_iff {x : ℕ} {φ : Formula P R} {w : W} {g : PartialAssign ℕ D} :
    eval M (.ex x φ) w g = -1 ↔
      eval M φ w g ≠ 1 ∧ ∀ a, eval M φ w (g.update x a) = -1 := by
  simp only [eval]
  split_ifs <;> simp [*]

theorem ne_bot_of_eval_ex_pred {p : P} {x : ℕ} {w : W} {g : PartialAssign ℕ D}
    (h : eval M (.ex x (.pred p x)) w g = 1) : g x ≠ ⊥ := by
  obtain ⟨d, hd, -⟩ := eval_pred_eq_true_iff.1 (eval_ex_eq_true_iff.1 h)
  simp [hd]

/-! ### Truth conditions -/

theorem trueAt_conj_iff (T Q : P) (x : ℕ) (w : W) :
    TrueAt M (.and (.ex x (.pred T x)) (.pred Q x)) w ↔
      ∃ d, d ∈ M.pred T w ∧ d ∈ M.pred Q w := by
  constructor
  · rintro ⟨g, hg⟩
    rw [eval_and] at hg
    have h1 : eval M (.ex x (.pred T x)) w g = 1 := by
      cases h : eval M (.ex x (.pred T x)) w g <;> simp_all [meetMiddle]
    rw [h1, SignType.meetMiddle_one_left] at hg
    obtain ⟨d, hd, hT⟩ := eval_pred_eq_true_iff.1 (eval_ex_eq_true_iff.1 h1)
    obtain ⟨d', hd', hQ⟩ := eval_pred_eq_true_iff.1 hg
    rw [hd] at hd'
    exact ⟨d, hT, Flat.coe_inj.1 hd' ▸ hQ⟩
  · rintro ⟨d, hT, hQ⟩
    refine ⟨PartialAssign.single x d, ?_⟩
    rw [eval_and, eval_ex_eq_true_iff.2 (eval_pred_eq_true_iff.2 ⟨d, by simp, hT⟩),
      SignType.meetMiddle_one_left]
    exact eval_pred_eq_true_iff.2 ⟨d, by simp, hQ⟩

theorem trueAt_bathroom_iff (B F : P) (x : ℕ) (w : W) :
    TrueAt M (.or (.not (.ex x (.pred B x))) (.pred F x)) w ↔
      (∀ d, d ∉ M.pred B w) ∨ ∃ d, d ∈ M.pred B w ∧ d ∈ M.pred F w := by
  constructor
  · rintro ⟨g, hg⟩
    rw [eval_or, eval_not] at hg
    cases hE : eval M (.ex x (.pred B x)) w g with
    | zero => simp [hE, SignType.joinMiddle_zero_left] at hg
    | neg =>
      left
      intro d hd
      obtain ⟨-, hall⟩ := eval_ex_eq_false_iff.1 hE
      obtain ⟨d', hd', hnot⟩ := eval_pred_eq_false_iff.1 (hall d)
      rw [PartialAssign.update_self] at hd'
      exact hnot (Flat.coe_inj.1 hd' ▸ hd)
    | pos =>
      right
      rw [hE, SignType.pos_eq_one, SignType.joinMiddle_neg_one_left] at hg
      obtain ⟨d, hd, hB⟩ := eval_pred_eq_true_iff.1 (eval_ex_eq_true_iff.1 hE)
      obtain ⟨d', hd', hF⟩ := eval_pred_eq_true_iff.1 hg
      rw [hd] at hd'
      exact ⟨d, hB, Flat.coe_inj.1 hd' ▸ hF⟩
  · rintro (hnone | ⟨d, hB, hF⟩)
    · refine ⟨(⊥ : PartialAssign ℕ D), ?_⟩
      rw [eval_or, eval_not, eval_ex_eq_false_iff.2 ⟨?_, fun a ↦ ?_⟩]
      · rfl
      · rw [eval_pred_of_eq_bot rfl]; decide
      · exact eval_pred_eq_false_iff.2 ⟨a, PartialAssign.update_self _ _ _, hnone a⟩
    · refine ⟨PartialAssign.single x d, ?_⟩
      rw [eval_or, eval_not, eval_ex_eq_true_iff.2 (eval_pred_eq_true_iff.2 ⟨d, by simp, hB⟩),
        SignType.joinMiddle_neg_one_left]
      exact eval_pred_eq_true_iff.2 ⟨d, by simp, hF⟩

/-! ### Contexts and Transparency

Contexts are sets of pairs of a world and an assignment, singular in the simplified system and
plural in the full one; update, Transparency and felicity are defined once over the evaluation
`ev` of either system. -/

section Contexts

variable {A : Type*} (ev : Formula P R → W → A → SignType)

/-- The null context, all world–assignment pairs. -/
def nullCtx : Set (W × A) := Set.univ

/-- Stalnakerian update keeps the pairs of the context at which the accepted sentence is true. -/
def update (C : Set (W × A)) (φ : Formula P R) : Set (W × A) := {p ∈ C | ev φ p.1 p.2 = 1}

theorem isClassical_update (φ : Formula P R) :
    DynamicSemantics.CCP.IsClassical (update ev · φ) :=
  DynamicSemantics.CCP.isClassical_up {p : W × A | ev φ p.1 p.2 = 1}

/-- A frame is a sentence with the occurrence under test as a hole. -/
abbrev Frame (P R : Type*) := Formula P R → Formula P R

/-- The occurrence at the hole of `F` is transparent in `C` for the presupposition `π` when
filling the hole with *π ∧ φ* and with *φ* gives the same value throughout `C`, for every `φ`
(§2.2.2; in the full system §6.3, where `π` reads as *atomic(x)*). -/
def Transparent (C : Set (W × A)) (F : Frame P R) (π : Formula P R) : Prop :=
  ∀ φ : Formula P R, ∀ p ∈ C, ev (F (.and π φ)) p.1 p.2 = ev (F φ) p.1 p.2

end Contexts

theorem not_transparent_id_null [Nonempty W] (x : ℕ) :
    ¬ Transparent (eval M) nullCtx id (.valued x) := by
  intro h
  have := h (.not (.valued x)) (Classical.arbitrary W, (⊥ : PartialAssign ℕ D)) trivial
  simp only [id, eval_and, eval_not, eval_valued_bot] at this
  exact absurd this (by decide)

theorem transparent_id_of_valued {C : Set (W × PartialAssign ℕ D)} {x : ℕ}
    (hC : ∀ p ∈ C, p.2 x ≠ ⊥) :
    Transparent (eval M) C id (.valued x) := fun _ p hp ↦ by
  simp only [id, eval_and, eval_valued_of_ne_bot (hC p hp), SignType.meetMiddle_one_left]

theorem ne_bot_of_mem_update_ex {C : Set (W × PartialAssign ℕ D)} {T : P} {x : ℕ}
    {p : W × PartialAssign ℕ D}
    (hp : p ∈ update (eval M) C (.ex x (.pred T x))) : p.2 x ≠ ⊥ :=
  ne_bot_of_eval_ex_pred hp.2

theorem transparent_id_of_update_ex (C : Set (W × PartialAssign ℕ D)) (T : P) (x : ℕ) :
    Transparent (eval M) (update (eval M) C (.ex x (.pred T x))) id (.valued x) :=
  transparent_id_of_valued fun _ hp ↦ ne_bot_of_mem_update_ex hp

theorem transparent_forward_conj (C : Set (W × PartialAssign ℕ D)) (T : P) (x : ℕ) :
    Transparent (eval M) C (fun ψ ↦ .and (.ex x (.pred T x)) ψ) (.valued x) := fun φ p _ ↦ by
  simp only [eval_and]
  exact conj_transparency_parametric _ _ _ fun h ↦ eval_valued_of_ne_bot (ne_bot_of_eval_ex_pred h)

theorem not_transparent_reverse_conj [Nonempty W] (T : P) (x : ℕ) :
    ¬ Transparent (eval M) nullCtx (fun ψ ↦ .and ψ (.ex x (.pred T x))) (.valued x) := by
  intro h
  have := h (.pred T x) (Classical.arbitrary W, (⊥ : PartialAssign ℕ D)) trivial
  simp only [eval_and, eval_valued_bot, eval_pred_of_eq_bot (g := (⊥ : PartialAssign ℕ D)) rfl,
    SignType.meetMiddle_neg_one_left, SignType.meetMiddle_zero_left] at this
  exact absurd this (by decide)

theorem transparent_bathroom (C : Set (W × PartialAssign ℕ D)) (B : P) (x : ℕ) :
    Transparent (eval M) C (fun ψ ↦ .or (.not (.ex x (.pred B x))) ψ) (.valued x) := fun φ p _ ↦ by
  simp only [eval_or, eval_not]
  exact disj_transparency_parametric _ _ _ fun h ↦
    eval_valued_of_ne_bot (ne_bot_of_eval_ex_pred (SignType.neg_eq_neg_one_iff.1 h))

theorem not_transparent_reverse_bathroom (B : P) (x : ℕ) (hw : ∃ w d, d ∈ M.pred B w) :
    ¬ Transparent (eval M) nullCtx (fun ψ ↦ .or ψ (.not (.ex x (.pred B x)))) (.valued x) := by
  intro h
  obtain ⟨w, d, hd⟩ := hw
  have := h (.or (.valued x) (.not (.valued x))) (w, (⊥ : PartialAssign ℕ D)) trivial
  have hE : eval M (.ex x (.pred B x)) w (⊥ : PartialAssign ℕ D) = 0 := by
    cases hE : eval M (.ex x (.pred B x)) w (⊥ : PartialAssign ℕ D) with
    | zero => rfl
    | pos =>
      have := eval_ex_eq_true_iff.1 hE
      rw [eval_pred_of_eq_bot rfl] at this
      cases this
    | neg =>
      obtain ⟨-, hall⟩ := eval_ex_eq_false_iff.1 hE
      obtain ⟨d', hd', hnot⟩ := eval_pred_eq_false_iff.1 (hall d)
      rw [PartialAssign.update_self] at hd'
      exact (hnot (Flat.coe_inj.1 hd' ▸ hd)).elim
  simp only [eval_or, eval_and, eval_not, hE, eval_valued_bot,
    SignType.meetMiddle_neg_one_left] at this
  exact absurd this (by decide)

/-! ### The Transparency Condition for sentences and discourses -/

/-- The occurrences of free variables in the atoms of a formula, below the variables `B` bound
above them. Each is the frame holing the atom, paired with the presupposition tested there,
which is *valued(x)* for each free argument and *valued(x) ∧ valued(y)* for a relation whose two
arguments are free (§2.2.2, items 1–2). -/
def Formula.occurrences {P R : Type*} : List ℕ → Formula P R → List (Frame P R × Formula P R)
  | B, .pred _ x => if x ∈ B then [] else [(id, .valued x)]
  | B, .rel _ x y =>
    ((if x ∈ B then [] else [(id, .valued x)]) ++ if y ∈ B then [] else [(id, .valued y)]) ++
      if x ∉ B ∧ y ∉ B then [(id, .and (.valued x) (.valued y))] else []
  | _, .valued _ => []
  | B, .not φ => (φ.occurrences B).map (Prod.map ((Formula.not) ∘ ·) id)
  | B, .and φ ψ =>
      (φ.occurrences B).map (Prod.map ((fun χ : Formula P R ↦ Formula.and χ ψ) ∘ ·) id) ++
      (ψ.occurrences B).map (Prod.map ((Formula.and φ) ∘ ·) id)
  | B, .or φ ψ =>
      (φ.occurrences B).map (Prod.map ((fun χ : Formula P R ↦ Formula.or χ ψ) ∘ ·) id) ++
      (ψ.occurrences B).map (Prod.map ((Formula.or φ) ∘ ·) id)
  | B, .ex x φ => (φ.occurrences (x :: B)).map (Prod.map ((Formula.ex x) ∘ ·) id)
  | B, .all x φ => (φ.occurrences (x :: B)).map (Prod.map ((Formula.all x) ∘ ·) id)
  | B, .strong φ => (φ.occurrences B).map (Prod.map ((Formula.strong) ∘ ·) id)

section Felicity

variable {A : Type*} (ev : Formula P R → W → A → SignType)

/-- A sentence is felicitous in `C` when Transparency holds in `C` at every occurrence of every
free variable (§2.2.2, item 4; §6.3). -/
def Felicitous (C : Set (W × A)) (S : Formula P R) : Prop :=
  ∀ o ∈ S.occurrences [], Transparent ev C o.1 o.2

/-- A discourse is felicitous in `C` when each sentence is felicitous in the context updated with
the sentences before it (§2.2.1, fn. 21). -/
def FelicitousDiscourse (C : Set (W × A)) : List (Formula P R) → Prop
  | [] => True
  | S :: Ss => Felicitous ev C S ∧ FelicitousDiscourse (update ev C S) Ss

end Felicity

/-- *It is purple* out of the blue is infelicitous (§3.1). -/
theorem not_felicitous_pred_null [Nonempty W] (Q : P) (x : ℕ) :
    ¬ Felicitous (eval M) nullCtx (.pred Q x) := fun h ↦
  not_transparent_id_null x (h (id, .valued x) (by simp [Formula.occurrences]))

/-- *A table is in the room. It is purple.* is felicitous in every context (§3.1). -/
theorem felicitousDiscourse_ex_pred (C : Set (W × PartialAssign ℕ D)) (T Q : P) (x : ℕ) :
    FelicitousDiscourse (eval M) C [.ex x (.pred T x), .pred Q x] := by
  refine ⟨fun o ho ↦ by simp [Formula.occurrences] at ho, fun o ho ↦ ?_, trivial⟩
  simp only [Formula.occurrences, List.not_mem_nil, ite_false, List.mem_singleton] at ho
  subst ho
  exact transparent_id_of_update_ex C T x

/-- *A table is in the room and it is purple* is felicitous in every context ((9)). -/
theorem felicitous_forward_conj (C : Set (W × PartialAssign ℕ D)) (T Q : P) (x : ℕ) :
    Felicitous (eval M) C (.and (.ex x (.pred T x)) (.pred Q x)) := by
  intro o ho
  simp [Formula.occurrences] at ho
  subst ho
  exact transparent_forward_conj C T x

/-- *It is purple and a table is in the room* is infelicitous in the null context ((10)). -/
theorem not_felicitous_reverse_conj [Nonempty W] (T Q : P) (x : ℕ) :
    ¬ Felicitous (eval M) nullCtx (.and (.pred Q x) (.ex x (.pred T x))) := by
  intro h
  refine not_transparent_reverse_conj (M := M) T x ?_
  intro φ p hp
  have := h (fun ψ ↦ .and ψ (.ex x (.pred T x)), .valued x) (by simp [Formula.occurrences])
  exact this φ p hp

/-- The bathroom sentence is felicitous in every context ((11)). -/
theorem felicitous_bathroom (C : Set (W × PartialAssign ℕ D)) (B H : P) (x : ℕ) :
    Felicitous (eval M) C (.or (.not (.ex x (.pred B x))) (.pred H x)) := by
  intro o ho
  simp [Formula.occurrences] at ho
  subst ho
  exact transparent_bathroom C B x

/-- The reversed bathroom sentence is infelicitous in the null context, where there could be a
bathroom ((12)). -/
theorem not_felicitous_reverse_bathroom (B H : P) (x : ℕ) (hw : ∃ w d, d ∈ M.pred B w) :
    ¬ Felicitous (eval M) nullCtx (.or (.pred H x) (.not (.ex x (.pred B x)))) := fun h ↦
  not_transparent_reverse_bathroom B x hw
    (h (fun χ ↦ .or χ (.not (.ex x (.pred B x))), .valued x) (by simp [Formula.occurrences]))

/-! ### Novelty -/

theorem eval_and_ex_ex_eq_true_iff (p q : P) (x : ℕ) (w : W) (g : PartialAssign ℕ D) :
    eval M (.and (.ex x (.pred p x)) (.ex x (.pred q x))) w g = 1 ↔
      eval M (.ex x (.and (.pred p x) (.pred q x))) w g = 1 := by
  rw [eval_ex_eq_true_iff, eval_and, eval_and]
  constructor
  · intro h
    have h1 : eval M (.ex x (.pred p x)) w g = 1 := by
      cases h1 : eval M (.ex x (.pred p x)) w g <;> simp_all [meetMiddle]
    rw [h1, SignType.meetMiddle_one_left, eval_ex_eq_true_iff] at h
    rw [eval_ex_eq_true_iff.1 h1, SignType.meetMiddle_one_left, h]
  · intro h
    have h1 : eval M (.pred p x) w g = 1 := by
      cases h1 : eval M (.pred p x) w g <;> simp_all [meetMiddle]
    rw [h1, SignType.meetMiddle_one_left] at h
    rw [eval_ex_eq_true_iff.2 h1, SignType.meetMiddle_one_left, eval_ex_eq_true_iff.2 h]

theorem not_novel_repeat (p q : P) (x : ℕ) :
    ¬ Novel [(Formula.ex x (.pred p x) : Formula P R), .ex x (.pred q x)] := by
  simp [Novel, Formula.binders]

theorem novel_fresh (p q : P) {x y : ℕ} (hxy : x ≠ y) :
    Novel [(Formula.ex x (.pred p x) : Formula P R), .ex y (.pred q y)] := by
  simp [Novel, Formula.binders, hxy]

theorem not_novel_of_mem_binders {S₁ S₂ : Formula P R} {x : ℕ} (h₁ : x ∈ S₁.binders)
    (h₂ : x ∈ S₂.binders) : ¬ Novel [S₁, S₂] := by
  intro h
  simp only [Novel, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  exact List.disjoint_of_nodup_append h h₁ h₂

/-- *Either the room is locked, or a female guitarist is playing. A woman is singing.* cannot
reuse the indefinite's variable ((16)). -/
theorem not_novel_16 (L φ ψ : Formula P R) (x : ℕ) : ¬ Novel [.or L (.ex x φ), .ex x ψ] :=
  not_novel_of_mem_binders (x := x) (by simp [Formula.binders]) (by simp [Formula.binders])

/-- A Stone disjunction with one variable, *Matt bought a train ticket or an airplane ticket. It
was expensive.*, violates Novelty (fn. 15). -/
theorem not_novel_stone (T A E : P) (x : ℕ) :
    ¬ Novel [(Formula.or (.ex x (.pred T x)) (.ex x (.pred A x)) : Formula P R), .pred E x] := by
  simp [Novel, Formula.binders]

/-! ### The failure of covariation -/

theorem trueAt_notExNotEx_iff [Nonempty D] (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAt M (.not (.ex x (.not (.ex y (.rel S x y))))) w ↔
      ∃ b, ∀ a, (a, b) ∈ M.rel S w := by
  have key : ∀ (g : PartialAssign ℕ D) (a : D),
      eval M (.not (.ex y (.rel S x y))) w (g.update x a) = -1 ↔
        ∃ b : D, g y = ↑b ∧ (a, b) ∈ M.rel S w := by
    intro g a
    rw [eval_not, SignType.neg_eq_neg_one_iff, eval_ex_eq_true_iff]
    cases hy : g y with
    | bot => simp [eval, hy, PartialAssign.update_of_ne hxy.symm]
    | coe b => simp [eval, hy, PartialAssign.update_of_ne hxy.symm]
  constructor
  · rintro ⟨g, hg⟩
    rw [eval_not, SignType.neg_eq_one_iff, eval_ex_eq_false_iff] at hg
    obtain ⟨-, hall⟩ := hg
    obtain ⟨a₀⟩ := ‹Nonempty D›
    obtain ⟨b, hb, -⟩ := (key g a₀).1 (hall a₀)
    refine ⟨b, fun a ↦ ?_⟩
    obtain ⟨b', hb', hS⟩ := (key g a).1 (hall a)
    rw [hb] at hb'
    exact Flat.coe_inj.1 hb' ▸ hS
  · rintro ⟨b, hb⟩
    refine ⟨PartialAssign.single y b, ?_⟩
    rw [eval_not, SignType.neg_eq_one_iff, eval_ex_eq_false_iff]
    refine ⟨fun hne ↦ ?_, fun a ↦ (key _ a).2 ⟨b, by simp, hb a⟩⟩
    rw [eval_not, SignType.neg_eq_one_iff, eval_ex_eq_false_iff] at hne
    obtain ⟨a₀⟩ := ‹Nonempty D›
    have := hne.2 a₀
    simp [eval, PartialAssign.update_of_ne hxy, PartialAssign.single_eq_of_ne hxy] at this

/-! ### The full system: plural assignments -/

variable (M) in
open Classical in
/-- Evaluation at a world and a plural assignment. A predicate of a variable is defined when
the assignments valuing the variable agree, and `valued` now reads as the paper's *atomic*;
the existential is false only when the plural assignment covers the domain and every
restriction falsifies the scope; the universal is true under that coverage when every
restriction verifies the scope; the strong-truth operator is true when its argument is true
here and false at no plural assignment, false when its argument is false here and true at no
plural assignment. -/
noncomputable def evalP : Formula P R → W → PluralAssign ℕ D → SignType
  | .pred p x, w, G =>
    if ∃ d, G.value x = {d} ∧ d ∈ M.pred p w then 1
    else if ∃ d, G.value x = {d} ∧ d ∉ M.pred p w then -1
    else 0
  | .rel r x y, w, G =>
    if ∃ a b, G.value x = {a} ∧ G.value y = {b} ∧ (a, b) ∈ M.rel r w then 1
    else if ∃ a b, G.value x = {a} ∧ G.value y = {b} ∧ (a, b) ∉ M.rel r w then -1
    else 0
  | .valued x, _, G => ofProp (∃ d, G.value x = {d})
  | .not φ, w, G => -evalP φ w G
  | .and φ ψ, w, G => meetMiddle (evalP φ w G) (evalP ψ w G)
  | .or φ ψ, w, G => joinMiddle (evalP φ w G) (evalP ψ w G)
  | .ex x φ, w, G =>
    if evalP φ w G = 1 then 1
    else if ∀ a, (G.restrict x a).Nonempty ∧ evalP φ w (G.restrict x a) = -1 then -1
    else 0
  | .all x φ, w, G =>
    if ∀ a, (G.restrict x a).Nonempty ∧ evalP φ w (G.restrict x a) = 1 then 1
    else if (∀ a, (G.restrict x a).Nonempty) ∧ ∃ a, evalP φ w (G.restrict x a) = -1 then
      (-1)
    else 0
  | .strong φ, w, G =>
    if evalP φ w G = 1 ∧ ∀ G', evalP φ w G' ≠ -1 then 1
    else if evalP φ w G = -1 ∧ ∀ G', evalP φ w G' ≠ 1 then -1
    else 0

variable (M) in
/-- A sentence is weakly true at a world when some plural assignment makes it true. -/
def TrueAtP (φ : Formula P R) (w : W) : Prop := ∃ G : PluralAssign ℕ D, evalP M φ w G = 1

variable (M) in
/-- A sentence is strongly true at a world when some plural assignment makes it true and none makes
it false. -/
def StronglyTrueAt (φ : Formula P R) (w : W) : Prop :=
  TrueAtP M φ w ∧ ∀ G : PluralAssign ℕ D, evalP M φ w G ≠ -1

theorem StronglyTrueAt.trueAtP {φ : Formula P R} {w : W} (h : StronglyTrueAt M φ w) :
    TrueAtP M φ w :=
  h.1

section Lemmas

variable {p : P} {r : R} {x y : ℕ} {φ ψ : Formula P R} {w : W} {G : PluralAssign ℕ D}

theorem evalP_pred_eq_true_iff :
    evalP M (.pred p x) w G = 1 ↔ ∃ d, G.value x = {d} ∧ d ∈ M.pred p w := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem evalP_pred_eq_false_iff :
    evalP M (.pred p x) w G = -1 ↔ ∃ d, G.value x = {d} ∧ d ∉ M.pred p w := by
  simp only [evalP]
  split_ifs with h1 h2
  · refine iff_of_false (by decide) ?_
    rintro ⟨d', hd', hn⟩
    obtain ⟨d, hd, hm⟩ := h1
    exact hn (by rw [Set.singleton_injective (hd'.symm.trans hd)]; exact hm)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

theorem evalP_rel_eq_true_iff :
    evalP M (.rel r x y) w G = 1 ↔
      ∃ a b, G.value x = {a} ∧ G.value y = {b} ∧ (a, b) ∈ M.rel r w := by
  simp only [evalP]
  split_ifs with h1 h2
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

theorem evalP_rel_eq_false_iff :
    evalP M (.rel r x y) w G = -1 ↔
      ∃ a b, G.value x = {a} ∧ G.value y = {b} ∧ (a, b) ∉ M.rel r w := by
  simp only [evalP]
  split_ifs with h1 h2
  · refine iff_of_false (by decide) ?_
    rintro ⟨a', b', ha', hb', hn⟩
    obtain ⟨a, b, ha, hb, hm⟩ := h1
    exact hn (by rw [Set.singleton_injective (ha'.symm.trans ha),
      Set.singleton_injective (hb'.symm.trans hb)]; exact hm)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

theorem evalP_valued_eq_true_iff : evalP M (.valued x) w G = 1 ↔ ∃ d, G.value x = {d} := by
  simp [evalP]

theorem evalP_valued_eq_false_iff : evalP M (.valued x) w G = -1 ↔ ¬ ∃ d, G.value x = {d} := by
  simp [evalP]

theorem evalP_not : evalP M (.not φ) w G = -evalP M φ w G := rfl

theorem evalP_and : evalP M (.and φ ψ) w G = meetMiddle (evalP M φ w G) (evalP M ψ w G) := rfl

theorem evalP_or : evalP M (.or φ ψ) w G = joinMiddle (evalP M φ w G) (evalP M ψ w G) := rfl

theorem evalP_ex_eq_true_iff : evalP M (.ex x φ) w G = 1 ↔ evalP M φ w G = 1 := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem evalP_ex_eq_false_iff :
    evalP M (.ex x φ) w G = -1 ↔ evalP M φ w G ≠ 1 ∧
      ∀ a, (G.restrict x a).Nonempty ∧ evalP M φ w (G.restrict x a) = -1 := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem evalP_all_eq_true_iff :
    evalP M (.all x φ) w G = 1 ↔
      ∀ a, (G.restrict x a).Nonempty ∧ evalP M φ w (G.restrict x a) = 1 := by
  simp only [evalP]
  split_ifs with h1 h2
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

theorem evalP_all_eq_false_iff :
    evalP M (.all x φ) w G = -1 ↔
      (∀ a, (G.restrict x a).Nonempty) ∧ ∃ a, evalP M φ w (G.restrict x a) = -1 := by
  simp only [evalP]
  split_ifs with h1 h2
  · refine iff_of_false (by decide) ?_
    rintro ⟨-, a, ha⟩
    rw [(h1 a).2] at ha
    cases ha
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

theorem evalP_strong_eq_true_iff :
    evalP M (.strong φ) w G = 1 ↔
      evalP M φ w G = 1 ∧ ∀ G', evalP M φ w G' ≠ -1 := by
  simp only [evalP]
  split_ifs <;> simp [*]

theorem singular_of_evalP_ex_pred (h : evalP M (.ex x (.pred p x)) w G = 1) :
    ∃ d, G.value x = {d} :=
  (evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 h)).elim fun _ h ↦ ⟨_, h.1⟩

theorem evalP_strong_eq_false_iff :
    evalP M (.strong φ) w G = -1 ↔
      evalP M φ w G = -1 ∧ ∀ G', evalP M φ w G' ≠ 1 := by
  simp only [evalP]
  split_ifs <;> simp [*]

end Lemmas

/-! ### Transparency in the full system -/

theorem transparentP_forward_conj (C : Set (W × PluralAssign ℕ D)) (T : P) (x : ℕ) :
    Transparent (evalP M) C (fun ψ ↦ .and (.ex x (.pred T x)) ψ) (.valued x) := fun φ p _ ↦ by
  simp only [evalP_and]
  exact conj_transparency_parametric _ _ _ fun h ↦
    evalP_valued_eq_true_iff.2 (singular_of_evalP_ex_pred h)

theorem transparentP_bathroom (C : Set (W × PluralAssign ℕ D)) (B : P) (x : ℕ) :
    Transparent (evalP M) C (fun ψ ↦ .or (.not (.ex x (.pred B x))) ψ) (.valued x) := fun φ p _ ↦ by
  simp only [evalP_or, evalP_not]
  exact disj_transparency_parametric _ _ _ fun h ↦
    evalP_valued_eq_true_iff.2 (singular_of_evalP_ex_pred (SignType.neg_eq_neg_one_iff.1 h))

theorem not_singular_of_covers {G : PluralAssign ℕ D} {x : ℕ} {a b : D} (hab : a ≠ b)
    (hcov : ∀ a, (G.restrict x a).Nonempty) : ¬ ∃ d, G.value x = {d} := by
  rintro ⟨d, hd⟩
  obtain ⟨_, hga⟩ := hcov a
  obtain ⟨_, hgb⟩ := hcov b
  exact hab ((PluralAssign.eq_of_mem_restrict hd hga).trans
    (PluralAssign.eq_of_mem_restrict hd hgb).symm)

theorem not_transparentP_forall_conj {a b : D} (hab : a ≠ b)
    {C : Set (W × PluralAssign ℕ D)} {P₀ : P} {x : ℕ}
    {w : W} {G : PluralAssign ℕ D} (hC : (w, G) ∈ C)
    (hall : evalP M (.all x (.pred P₀ x)) w G = 1) :
    ¬ Transparent (evalP M) C (fun ψ ↦ .and (.all x (.pred P₀ x)) ψ) (.valued x) := by
  intro h
  have hx : evalP M (.valued x) w G = -1 :=
    evalP_valued_eq_false_iff.2
      (not_singular_of_covers hab fun a ↦ ((evalP_all_eq_true_iff.1 hall) a).1)
  have := h (.not (.valued x)) (w, G) hC
  simp only [evalP_and, evalP_not, hall, hx, SignType.meetMiddle_one_left,
    SignType.meetMiddle_neg_one_left] at this
  exact absurd this (by decide)

variable (D) in
/-- The plural assignment mapping `x` to every individual, one row each. -/
def covering (x : ℕ) : PluralAssign ℕ D := Set.range (PartialAssign.single x)

theorem restrict_covering_nonempty (x : ℕ) (a : D) : ((covering D x).restrict x a).Nonempty :=
  ⟨PartialAssign.single x a, ⟨a, rfl⟩, by simp⟩

theorem not_transparentP_forall_conj_univ {a b : D} (hab : a ≠ b) {P₀ : P} (x : ℕ)
    (hw : ∃ w, ∀ d, d ∈ M.pred P₀ w) :
    ¬ Transparent (evalP M) Set.univ (fun ψ ↦ .and (.all x (.pred P₀ x)) ψ) (.valued x) := by
  obtain ⟨w, hw⟩ := hw
  refine not_transparentP_forall_conj hab (w := w) (G := covering D x) (Set.mem_univ _)
    (evalP_all_eq_true_iff.2 fun a ↦ ⟨restrict_covering_nonempty x a, ?_⟩)
  exact evalP_pred_eq_true_iff.2
    ⟨a, PluralAssign.value_restrict (restrict_covering_nonempty x a), hw a⟩

theorem evalP_ex_and_all_ne_true {a b : D} (hab : a ≠ b) (P₀ Q : P) (x : ℕ) (w : W)
    (G : PluralAssign ℕ D) :
    evalP M (.and (.ex x (.pred P₀ x)) (.all x (.pred Q x))) w G ≠ 1 := by
  intro h
  rw [evalP_and, SignType.meetMiddle_eq_one_iff] at h
  exact not_singular_of_covers hab (fun a ↦ ((evalP_all_eq_true_iff.1 h.2) a).1)
    (singular_of_evalP_ex_pred h.1)

/-! ### Truth conditions in the full system -/

theorem trueAtP_bathroom_iff (B F : P) (x : ℕ) (w : W) :
    TrueAtP M (.or (.not (.ex x (.pred B x))) (.pred F x)) w ↔
      (∀ d, d ∉ M.pred B w) ∨ ∃ d, d ∈ M.pred B w ∧ d ∈ M.pred F w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_or, evalP_not] at hG
    cases hE : evalP M (.ex x (.pred B x)) w G with
    | zero => simp [hE, SignType.joinMiddle_zero_left] at hG
    | neg =>
      left
      intro d hd
      obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 hE
      obtain ⟨hne, hfalse⟩ := hall d
      obtain ⟨d', hd', hn⟩ := evalP_pred_eq_false_iff.1 hfalse
      exact hn ((PluralAssign.value_restrict_eq_singleton_iff.1 hd').2 ▸ hd)
    | pos =>
      right
      rw [hE, SignType.pos_eq_one, SignType.joinMiddle_neg_one_left] at hG
      obtain ⟨d, hd, hB⟩ := evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 hE)
      obtain ⟨d', hd', hF⟩ := evalP_pred_eq_true_iff.1 hG
      exact ⟨d, hB, Set.singleton_injective (hd.symm.trans hd') ▸ hF⟩
  · rintro (hnone | ⟨d, hB, hF⟩)
    · refine ⟨covering D x, ?_⟩
      rw [evalP_or, evalP_not, evalP_ex_eq_false_iff.2 ⟨?_, fun a ↦ ?_⟩, neg_neg,
        SignType.joinMiddle_one_left]
      · rw [Ne, evalP_pred_eq_true_iff]
        rintro ⟨d, -, hd⟩
        exact hnone d hd
      · exact ⟨restrict_covering_nonempty x a, evalP_pred_eq_false_iff.2
          ⟨a, PluralAssign.value_restrict (restrict_covering_nonempty x a), hnone a⟩⟩
    · refine ⟨{PartialAssign.single x d}, ?_⟩
      have hsing : ({PartialAssign.single x d} : PluralAssign ℕ D).value x = {d} :=
        PluralAssign.value_singleton_eq_singleton_iff.2 (by simp)
      rw [evalP_or, evalP_not, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨d, hsing, hB⟩),
        SignType.joinMiddle_neg_one_left]
      exact evalP_pred_eq_true_iff.2 ⟨d, hsing, hF⟩

/-- The plural assignment pairing each individual `a` at `x` with `f a` at `y`. -/
def pairing (x y : ℕ) (f : D → D) : PluralAssign ℕ D :=
  Set.range fun a ↦ (PartialAssign.single x a).update y (f a)

theorem restrict_pairing {x y : ℕ} (hxy : x ≠ y) (f : D → D) (a : D) :
    ((pairing x y f).restrict x a).Nonempty ∧
      ((pairing x y f).restrict x a).value y = {f a} := by
  have hmem : ∀ a', (PartialAssign.single x a').update y (f a') ∈
      (pairing x y f).restrict x a ↔ a' = a := by
    intro a'
    constructor
    · rintro ⟨-, h⟩
      simpa [PartialAssign.update_of_ne hxy] using h
    · rintro rfl
      exact ⟨⟨a', rfl⟩, by simp [PartialAssign.update_of_ne hxy]⟩
  refine ⟨⟨_, (hmem a).2 rfl⟩, PluralAssign.value_eq_singleton_iff.2 ⟨⟨_, (hmem a).2 rfl, by simp⟩,
    ?_⟩⟩
  rintro g ⟨⟨a', rfl⟩, hga⟩ -
  rw [(hmem a').1 ⟨⟨a', rfl⟩, hga⟩]
  simp

theorem trueAtP_notExNotEx_iff [Nonempty D] (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAtP M (.not (.ex x (.not (.ex y (.rel S x y))))) w ↔
      ∀ a, ∃ b, (a, b) ∈ M.rel S w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_not, SignType.neg_eq_one_iff, evalP_ex_eq_false_iff] at hG
    intro a
    obtain ⟨hne, hfalse⟩ := hG.2 a
    rw [evalP_not, SignType.neg_eq_neg_one_iff, evalP_ex_eq_true_iff,
      evalP_rel_eq_true_iff] at hfalse
    obtain ⟨a', b, ha', hb, hS⟩ := hfalse
    exact ⟨b, (PluralAssign.value_restrict_eq_singleton_iff.1 ha').2 ▸ hS⟩
  · intro hS
    choose f hf using hS
    refine ⟨pairing x y f, ?_⟩
    rw [evalP_not, SignType.neg_eq_one_iff, evalP_ex_eq_false_iff]
    refine ⟨?_, fun a ↦ ?_⟩
    · rw [Ne, evalP_not, SignType.neg_eq_one_iff, evalP_ex_eq_false_iff]
      rintro ⟨-, hall⟩
      obtain ⟨a₀⟩ := ‹Nonempty D›
      obtain ⟨-, hfalse⟩ := hall (f a₀)
      obtain ⟨a', b', ha', hb', hn⟩ := evalP_rel_eq_false_iff.1 hfalse
      have hg₀ : (PartialAssign.single x a₀).update y (f a₀) ∈
          (pairing x y f).restrict y (f a₀) :=
        ⟨⟨a₀, rfl⟩, by simp⟩
      have hx : a₀ = a' :=
        PluralAssign.eq_of_mem_restrict ha' ⟨hg₀, by simp [PartialAssign.update_of_ne hxy]⟩
      rw [← hx, (PluralAssign.value_restrict_eq_singleton_iff.1 hb').2] at hn
      exact hn (hf a₀)
    · obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
      refine ⟨hne, ?_⟩
      rw [evalP_not, SignType.neg_eq_neg_one_iff, evalP_ex_eq_true_iff, evalP_rel_eq_true_iff]
      exact ⟨a, f a, PluralAssign.value_restrict hne, hsing, hf a⟩

theorem trueAtP_allEx_iff (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAtP M (.all x (.ex y (.rel S x y))) w ↔ ∀ a, ∃ b, (a, b) ∈ M.rel S w := by
  constructor
  · rintro ⟨G, hG⟩
    intro a
    obtain ⟨-, htrue⟩ := evalP_all_eq_true_iff.1 hG a
    obtain ⟨a', b, ha', hb, hS⟩ := evalP_rel_eq_true_iff.1 (evalP_ex_eq_true_iff.1 htrue)
    exact ⟨b, (PluralAssign.value_restrict_eq_singleton_iff.1 ha').2 ▸ hS⟩
  · intro hS
    choose f hf using hS
    refine ⟨pairing x y f, evalP_all_eq_true_iff.2 fun a ↦ ?_⟩
    obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
    exact ⟨hne, evalP_ex_eq_true_iff.2 (evalP_rel_eq_true_iff.2
      ⟨a, f a, PluralAssign.value_restrict hne, hsing, hf a⟩)⟩

theorem trueAtP_allEx_iff_notExNotEx [Nonempty D] (S : R) {x y : ℕ} (hxy : x ≠ y) (w : W) :
    TrueAtP M (.all x (.ex y (.rel S x y))) w ↔
      TrueAtP M (.not (.ex x (.not (.ex y (.rel S x y))))) w := by
  rw [trueAtP_allEx_iff S hxy, trueAtP_notExNotEx_iff S hxy]

/-! ### Weak and strong truth -/

theorem stronglyTrueAt_ex_iff (P₀ : P) (x : ℕ) (w : W) :
    StronglyTrueAt M (.ex x (.pred P₀ x)) w ↔ TrueAtP M (.ex x (.pred P₀ x)) w := by
  refine ⟨StronglyTrueAt.trueAtP, fun h ↦ ⟨h, fun G' hG' ↦ ?_⟩⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨d, -, hd⟩ := evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 hG)
  obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 hG'
  obtain ⟨-, hfalse⟩ := hall d
  obtain ⟨d', hd', hn⟩ := evalP_pred_eq_false_iff.1 hfalse
  exact hn (by rw [(PluralAssign.value_restrict_eq_singleton_iff.1 hd').2]; exact hd)

theorem trueAtP_not_stronglyTrueAt_conj (B F : P) (x : ℕ) (w : W) {b₁ b₂ : D}
    (h₁ : b₁ ∈ M.pred B w) (h₂ : b₂ ∈ M.pred B w) (hF₁ : b₁ ∈ M.pred F w)
    (hF₂ : b₂ ∉ M.pred F w) :
    TrueAtP M (.and (.ex x (.pred B x)) (.pred F x)) w ∧
      ¬ StronglyTrueAt M (.and (.ex x (.pred B x)) (.pred F x)) w := by
  have hs : ∀ d : D, ({PartialAssign.single x d} : PluralAssign ℕ D).value x = {d} :=
    fun d ↦ PluralAssign.value_singleton_eq_singleton_iff.2 (by simp)
  refine ⟨⟨{PartialAssign.single x b₁}, ?_⟩,
    fun h ↦ h.2 {PartialAssign.single x b₂} ?_⟩
  · rw [evalP_and, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨b₁, hs b₁, h₁⟩),
      SignType.meetMiddle_one_left]
    exact evalP_pred_eq_true_iff.2 ⟨b₁, hs b₁, hF₁⟩
  · rw [evalP_and, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨b₂, hs b₂, h₂⟩),
      SignType.meetMiddle_one_left]
    exact evalP_pred_eq_false_iff.2 ⟨b₂, hs b₂, hF₂⟩

theorem trueAtP_strong_iff (φ : Formula P R) (w : W) :
    TrueAtP M (.strong φ) w ↔ StronglyTrueAt M φ w := by
  constructor
  · rintro ⟨G, hG⟩
    obtain ⟨h1, h2⟩ := evalP_strong_eq_true_iff.1 hG
    exact ⟨⟨G, h1⟩, h2⟩
  · rintro ⟨⟨G, hG⟩, h⟩
    exact ⟨G, evalP_strong_eq_true_iff.2 ⟨hG, h⟩⟩

theorem evalP_strong_congr {φ ψ : Formula P R} {w : W}
    (h : ∀ G, evalP M φ w G = evalP M ψ w G) (G : PluralAssign ℕ D) :
    evalP M (.strong φ) w G = evalP M (.strong ψ) w G := by
  simp only [evalP]
  rw [funext h]

theorem evalP_strong_valued [Nonempty D] (x : ℕ) (w : W) (G : PluralAssign ℕ D) :
    evalP M (.strong (.valued x)) w G = 0 := by
  obtain ⟨d⟩ := ‹Nonempty D›
  have ht : evalP M (.valued x) w {PartialAssign.single x d} = 1 :=
    evalP_valued_eq_true_iff.2 ⟨d, PluralAssign.value_singleton_eq_singleton_iff.2 (by simp)⟩
  have hf : evalP M (.valued x) w ∅ = -1 :=
    evalP_valued_eq_false_iff.2 (by simp)
  cases h : evalP M (.strong (.valued x)) w G with
  | zero => rfl
  | pos => exact absurd hf ((evalP_strong_eq_true_iff.1 h).2 _)
  | neg => exact absurd ht ((evalP_strong_eq_false_iff.1 h).2 _)

theorem trueAtP_ex_and_strong_iff (S H : P) (x : ℕ) (w : W) :
    TrueAtP M (.and (.ex x (.pred S x)) (.strong (.pred H x))) w ↔
      (∃ d, d ∈ M.pred S w) ∧ ∀ d, d ∈ M.pred H w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_and, SignType.meetMiddle_eq_one_iff, evalP_ex_eq_true_iff,
      evalP_pred_eq_true_iff, evalP_strong_eq_true_iff] at hG
    obtain ⟨⟨d, -, hd⟩, -, hall⟩ := hG
    refine ⟨⟨d, hd⟩, fun d ↦ by_contra fun hn ↦ hall {PartialAssign.single x d} ?_⟩
    exact evalP_pred_eq_false_iff.2 ⟨d, PluralAssign.value_singleton_eq_singleton_iff.2 (by simp),
      hn⟩
  · rintro ⟨⟨d, hd⟩, hall⟩
    have hs : ({PartialAssign.single x d} : PluralAssign ℕ D).value x = {d} :=
      PluralAssign.value_singleton_eq_singleton_iff.2 (by simp)
    refine ⟨{PartialAssign.single x d}, ?_⟩
    rw [evalP_and, SignType.meetMiddle_eq_one_iff, evalP_ex_eq_true_iff,
      evalP_strong_eq_true_iff]
    refine ⟨evalP_pred_eq_true_iff.2 ⟨d, hs, hd⟩, evalP_pred_eq_true_iff.2 ⟨d, hs, hall d⟩,
      fun G' hG' ↦ ?_⟩
    obtain ⟨d', -, hn⟩ := evalP_pred_eq_false_iff.1 hG'
    exact hn (hall d')

theorem not_transparentP_ex_and_strong {C : Set (W × PluralAssign ℕ D)} {S : P} {x : ℕ} {w : W}
    {G : PluralAssign ℕ D} (hC : (w, G) ∈ C) (hS : evalP M (.ex x (.pred S x)) w G = 1) :
    ¬ Transparent (evalP M) C (fun ψ ↦ .and (.ex x (.pred S x)) (.strong ψ)) (.valued x) := by
  intro h
  obtain ⟨d, -⟩ := singular_of_evalP_ex_pred hS
  have : Nonempty D := ⟨d⟩
  have htaut : ∀ G', evalP M (.or (.valued x) (.not (.valued x))) w G' = 1 := by
    intro G'
    rw [evalP_or, evalP_not]
    cases hv : evalP M (.valued x) w G' with
    | zero => exact absurd hv (by simp [evalP])
    | pos | neg => rfl
  have hconj : ∀ G', evalP M (.and (.valued x) (.or (.valued x) (.not (.valued x)))) w G' =
      evalP M (.valued x) w G' := fun G' ↦ by
    rw [evalP_and, htaut, SignType.meetMiddle_one_right]
  have := h (.or (.valued x) (.not (.valued x))) (w, G) hC
  simp only [evalP_and, hS, SignType.meetMiddle_one_left, evalP_strong_congr hconj,
    evalP_strong_valued, evalP_strong_eq_true_iff.2 ⟨htaut G, fun G' ↦ by rw [htaut G']; decide⟩]
    at this
  exact absurd this (by decide)

/-! ### The Transparency Condition in the full system -/

section Full

variable {x y : ℕ} {w : W}

open Classical in
theorem evalP_all_congr {φ ψ : Formula P R} {G : PluralAssign ℕ D}
    (h : ∀ a, evalP M φ w (G.restrict x a) = evalP M ψ w (G.restrict x a)) :
    evalP M (.all x φ) w G = evalP M (.all x ψ) w G := by
  simp only [evalP, h]

/-- *Everyone read something and everyone liked it* is true at a world exactly when everyone read
something they liked ((27)). -/
theorem trueAtP_qs_iff (Rd L : R) (hxy : x ≠ y) :
    TrueAtP M (.and (.all x (.ex y (.rel Rd x y))) (.all x (.rel L x y))) w ↔
      ∀ a, ∃ b, (a, b) ∈ M.rel Rd w ∧ (a, b) ∈ M.rel L w := by
  constructor
  · rintro ⟨G, hG⟩ a
    rw [evalP_and, SignType.meetMiddle_eq_one_iff] at hG
    obtain ⟨-, h1⟩ := evalP_all_eq_true_iff.1 hG.1 a
    obtain ⟨-, h2⟩ := evalP_all_eq_true_iff.1 hG.2 a
    obtain ⟨a₁, b₁, ha₁, hb₁, hR⟩ := evalP_rel_eq_true_iff.1 (evalP_ex_eq_true_iff.1 h1)
    obtain ⟨a₂, b₂, ha₂, hb₂, hL⟩ := evalP_rel_eq_true_iff.1 h2
    rw [(PluralAssign.value_restrict_eq_singleton_iff.1 ha₁).2] at hR
    rw [(PluralAssign.value_restrict_eq_singleton_iff.1 ha₂).2,
      ← Set.singleton_injective (hb₁.symm.trans hb₂)] at hL
    exact ⟨b₁, hR, hL⟩
  · intro h
    choose f hf using h
    refine ⟨pairing x y f, ?_⟩
    rw [evalP_and, SignType.meetMiddle_eq_one_iff]
    refine ⟨evalP_all_eq_true_iff.2 fun a ↦ ?_, evalP_all_eq_true_iff.2 fun a ↦ ?_⟩
    · obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
      exact ⟨hne, evalP_ex_eq_true_iff.2 (evalP_rel_eq_true_iff.2
        ⟨a, f a, PluralAssign.value_restrict hne, hsing, (hf a).1⟩)⟩
    · obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
      exact ⟨hne, evalP_rel_eq_true_iff.2
        ⟨a, f a, PluralAssign.value_restrict hne, hsing, (hf a).2⟩⟩

/-- The pronoun of quantificational subordination satisfies Transparency in every context
((28)). -/
theorem felicitousP_qs (C : Set (W × PluralAssign ℕ D)) (Rd L : R) (hxy : x ≠ y) :
    Felicitous (evalP M) C (.and (.all x (.ex y (.rel Rd x y))) (.all x (.rel L x y))) := by
  intro o ho
  simp [Formula.occurrences, hxy, hxy.symm] at ho
  subst ho
  intro φ p _
  simp only [Function.comp, evalP_and]
  refine SignType.meetMiddle_congr_right fun h ↦ evalP_all_congr fun a ↦ ?_
  obtain ⟨-, h1⟩ := evalP_all_eq_true_iff.1 h a
  obtain ⟨-, b, -, hb, -⟩ := evalP_rel_eq_true_iff.1 (evalP_ex_eq_true_iff.1 h1)
  rw [evalP_and, evalP_valued_eq_true_iff.2 ⟨_, hb⟩, SignType.meetMiddle_one_left]

/-- Over a domain with two individuals *every student came. He …* is infelicitous in the null
context, because a universal does not license a singular pronoun ((21)–(22)). -/
theorem not_felicitousP_forall_conj {a b : D} (hab : a ≠ b) {P₀ Q : P}
    (hw : ∃ w, ∀ d, d ∈ M.pred P₀ w) :
    ¬ Felicitous (evalP M) Set.univ (.and (.all x (.pred P₀ x)) (.pred Q x)) := fun h ↦
  not_transparentP_forall_conj_univ hab x hw
    (h (fun χ ↦ .and (.all x (.pred P₀ x)) χ, .valued x) (by simp [Formula.occurrences]))

/-- *A linguist came and not every linguist smiled*, with one variable, is never true over a
domain with two individuals ((23)). -/
theorem evalP_ex_and_not_all_ne_true {a b : D} (hab : a ≠ b) (P₀ Q : P) (G : PluralAssign ℕ D) :
    evalP M (.and (.ex x (.pred P₀ x)) (.not (.all x (.pred Q x)))) w G ≠ 1 := by
  intro h
  rw [evalP_and, SignType.meetMiddle_eq_one_iff, evalP_not, SignType.neg_eq_one_iff] at h
  exact not_singular_of_covers hab (evalP_all_eq_false_iff.1 h.2).1 (singular_of_evalP_ex_pred h.1)

/-- `∀x P(x)` and `¬∃x¬P(x)` differ in falsity. Where `x` covers a domain with two individuals, one
of which is not a `P`, the universal is false and the negated existential undefined (Remark 4). -/
theorem evalP_all_false_and_not_ex_not_indet {a b : D} (hab : a ≠ b) (P₀ : P)
    (hd : ∃ d, d ∉ M.pred P₀ w) :
    evalP M (.all x (.pred P₀ x)) w (covering D x) = -1 ∧
      evalP M (.not (.ex x (.not (.pred P₀ x)))) w (covering D x) = 0 := by
  obtain ⟨d, hd⟩ := hd
  have hns : ¬ ∃ d, (covering D x).value x = {d} :=
    not_singular_of_covers hab (restrict_covering_nonempty x)
  refine ⟨evalP_all_eq_false_iff.2 ⟨restrict_covering_nonempty x, d, evalP_pred_eq_false_iff.2
    ⟨d, PluralAssign.value_restrict (restrict_covering_nonempty x d), hd⟩⟩, ?_⟩
  rw [evalP_not]
  cases h : evalP M (.ex x (.not (.pred P₀ x))) w (covering D x) with
  | zero => rfl
  | pos =>
    have := evalP_ex_eq_true_iff.1 h
    rw [evalP_not, SignType.neg_eq_one_iff, evalP_pred_eq_false_iff] at this
    obtain ⟨d', hd', -⟩ := this
    exact absurd ⟨_, hd'⟩ hns
  | neg =>
    obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 h
    have hf := (hall d).2
    rw [evalP_not, SignType.neg_eq_neg_one_iff, evalP_pred_eq_true_iff] at hf
    obtain ⟨d', hd', hm⟩ := hf
    rw [(PluralAssign.value_restrict_eq_singleton_iff.1 hd').2] at hm
    exact absurd hm hd

/-- *Not every male student came. He stayed home.* is infelicitous, because the negated universal
makes `x` cover the domain, so the pronoun's atomicity fails (fn. 19). -/
theorem not_felicitousDiscourseP_not_all {a b : D} (hab : a ≠ b) (P₀ Q : P)
    (hd : ∃ d, d ∉ M.pred P₀ w) :
    ¬ FelicitousDiscourse (evalP M) Set.univ [.not (.all x (.pred P₀ x)), .pred Q x] := by
  rintro ⟨-, h, -⟩
  have hmem : (w, covering D x) ∈ update (evalP M) Set.univ (.not (.all x (.pred P₀ x))) := by
    refine ⟨trivial, ?_⟩
    rw [evalP_not, (evalP_all_false_and_not_ex_not_indet hab P₀ hd).1]; rfl
  have := h (id, .valued x) (by simp [Formula.occurrences]) (.or (.valued x) (.not (.valued x)))
    _ hmem
  have hns : ¬ ∃ d, (covering D x).value x = {d} :=
    not_singular_of_covers hab (restrict_covering_nonempty x)
  simp only [id, evalP_and, evalP_or, evalP_not, evalP_valued_eq_false_iff.2 hns] at this
  exact absurd this (by decide)

end Full

/-! ### Restrictors, donkey sentences, and strong truth -/

section Rows

variable {x y : ℕ} {w : W}

theorem restrict_iUnion_rows {rows : D → PluralAssign ℕ D} (h : ∀ e, ∀ g ∈ rows e, g x = ↑e)
    (e : D) : PluralAssign.restrict (⋃ e, rows e) x e = rows e := by
  ext g
  simp only [PluralAssign.mem_restrict, Set.mem_iUnion]
  refine ⟨fun ⟨⟨e', hg⟩, hgx⟩ ↦ ?_, fun hg ↦ ⟨⟨e, hg⟩, h e g hg⟩⟩
  rwa [Flat.coe_inj.1 ((h e' g hg).symm.trans hgx)] at hg

theorem update_single_apply_left (hxy : x ≠ y) (e v : D) :
    (PartialAssign.single x e).update y v x = ↑e := by
  simp [PartialAssign.update_of_ne hxy]

/-- *Every student read a book and every student liked it* is true at a world exactly when every
student read a book they liked ((31)). -/
theorem trueAtP_qs_restricted_iff [Nonempty D] (S B : P) (Rd L : R) (hxy : x ≠ y) :
    TrueAtP M (.and (.all x (.or (.not (.pred S x)) (.ex y (.and (.pred B y) (.rel Rd x y)))))
      (.all x (.or (.not (.pred S x)) (.rel L x y)))) w ↔
      ∀ a ∈ M.pred S w, ∃ b ∈ M.pred B w, (a, b) ∈ M.rel Rd w ∧ (a, b) ∈ M.rel L w := by
  constructor
  · rintro ⟨G, hG⟩ a ha
    rw [evalP_and, SignType.meetMiddle_eq_one_iff] at hG
    obtain ⟨hne, h1⟩ := evalP_all_eq_true_iff.1 hG.1 a
    obtain ⟨-, h2⟩ := evalP_all_eq_true_iff.1 hG.2 a
    have hS : evalP M (.not (.pred S x)) w (G.restrict x a) = -1 := by
      rw [evalP_not, SignType.neg_eq_neg_one_iff]
      exact evalP_pred_eq_true_iff.2 ⟨a, PluralAssign.value_restrict hne, ha⟩
    rw [evalP_or, hS, SignType.joinMiddle_neg_one_left, evalP_ex_eq_true_iff, evalP_and,
      SignType.meetMiddle_eq_one_iff] at h1
    rw [evalP_or, hS, SignType.joinMiddle_neg_one_left] at h2
    obtain ⟨b, hb, hB⟩ := evalP_pred_eq_true_iff.1 h1.1
    obtain ⟨a₁, b₁, ha₁, hb₁, hR⟩ := evalP_rel_eq_true_iff.1 h1.2
    obtain ⟨a₂, b₂, ha₂, hb₂, hL⟩ := evalP_rel_eq_true_iff.1 h2
    rw [(PluralAssign.value_restrict_eq_singleton_iff.1 ha₁).2,
      ← Set.singleton_injective (hb.symm.trans hb₁)] at hR
    rw [(PluralAssign.value_restrict_eq_singleton_iff.1 ha₂).2,
      ← Set.singleton_injective (hb.symm.trans hb₂)] at hL
    exact ⟨b, hB, hR, hL⟩
  · intro h
    have h' : ∀ a, ∃ b, a ∈ M.pred S w →
        b ∈ M.pred B w ∧ (a, b) ∈ M.rel Rd w ∧ (a, b) ∈ M.rel L w := fun a ↦ by
      by_cases ha : a ∈ M.pred S w
      · obtain ⟨b, hb⟩ := h a ha
        exact ⟨b, fun _ ↦ hb⟩
      · exact ⟨Classical.arbitrary D, fun h ↦ absurd h ha⟩
    choose f hf using h'
    refine ⟨pairing x y f, ?_⟩
    rw [evalP_and, SignType.meetMiddle_eq_one_iff]
    refine ⟨evalP_all_eq_true_iff.2 fun a ↦ ?_, evalP_all_eq_true_iff.2 fun a ↦ ?_⟩ <;>
    · obtain ⟨hne, hsing⟩ := restrict_pairing hxy f a
      have hsx := PluralAssign.value_restrict hne
      refine ⟨hne, ?_⟩
      by_cases ha : a ∈ M.pred S w
      · obtain ⟨hB, hR, hL⟩ := hf a ha
        rw [evalP_or, evalP_not, evalP_pred_eq_true_iff.2 ⟨a, hsx, ha⟩, 
          SignType.joinMiddle_neg_one_left]
        first
        | exact evalP_ex_eq_true_iff.2 (by
            rw [evalP_and, SignType.meetMiddle_eq_one_iff]
            exact ⟨evalP_pred_eq_true_iff.2 ⟨f a, hsing, hB⟩,
              evalP_rel_eq_true_iff.2 ⟨a, f a, hsx, hsing, hR⟩⟩)
        | exact evalP_rel_eq_true_iff.2 ⟨a, f a, hsx, hsing, hL⟩
      · rw [evalP_or, evalP_not, evalP_pred_eq_false_iff.2 ⟨a, hsx, ha⟩, neg_neg,
          SignType.joinMiddle_one_left]

/-- The pronoun of *every student read a book and every student liked it* satisfies
Transparency in every context ((32)). -/
theorem felicitousP_qs_restricted (C : Set (W × PluralAssign ℕ D)) (S B : P) (Rd L : R)
    (hxy : x ≠ y) :
    Felicitous (evalP M) C
      (.and (.all x (.or (.not (.pred S x)) (.ex y (.and (.pred B y) (.rel Rd x y)))))
        (.all x (.or (.not (.pred S x)) (.rel L x y)))) := by
  intro o ho
  simp [Formula.occurrences, hxy, hxy.symm] at ho
  subst ho
  intro φ p _
  simp only [Function.comp, evalP_and]
  refine SignType.meetMiddle_congr_right fun h ↦ evalP_all_congr fun a ↦ ?_
  rw [evalP_or, evalP_or, evalP_and]
  refine disj_transparency_parametric _ _ _ fun hS ↦ ?_
  obtain ⟨-, h1⟩ := evalP_all_eq_true_iff.1 h a
  rw [evalP_or, hS, SignType.joinMiddle_neg_one_left, evalP_ex_eq_true_iff, evalP_and,
    SignType.meetMiddle_eq_one_iff] at h1
  obtain ⟨b, hb, -⟩ := evalP_pred_eq_true_iff.1 h1.1
  exact evalP_valued_eq_true_iff.2 ⟨_, hb⟩

/-- The pronoun of *every student read a book and everyone liked it* fails Transparency in the null
context at a world with a non-student where every student read a book, since a plural assignment can
leave the non-student's book unsettled ((33)–(34)). -/
theorem not_felicitousP_qs_everyone {c d : D} (hcd : c ≠ d) (S B : P) (Rd L : R) (hxy : x ≠ y)
    {e₀ : D} (he₀ : e₀ ∉ M.pred S w)
    (hS : ∀ s ∈ M.pred S w, ∃ b ∈ M.pred B w, (s, b) ∈ M.rel Rd w) :
    ¬ Felicitous (evalP M) Set.univ
      (.and (.all x (.or (.not (.pred S x)) (.ex y (.and (.pred B y) (.rel Rd x y)))))
        (.all x (.rel L x y))) := by
  classical
  intro hfel
  have hT := hfel ((Formula.and (.all x (.or (.not (.pred S x))
    (.ex y (.and (.pred B y) (.rel Rd x y)))))) ∘ Formula.all x, .valued y)
    (by simp [Formula.occurrences, hxy, hxy.symm])
  have h' : ∀ s, ∃ b, s ∈ M.pred S w → b ∈ M.pred B w ∧ (s, b) ∈ M.rel Rd w := fun s ↦ by
    by_cases hs : s ∈ M.pred S w
    · obtain ⟨b, hb⟩ := hS s hs
      exact ⟨b, fun _ ↦ hb⟩
    · exact ⟨c, fun h ↦ absurd h hs⟩
  choose f hf using h'
  let row : D → D → PartialAssign ℕ D := fun e v ↦ (PartialAssign.single x e).update y v
  let rows : D → PluralAssign ℕ D := fun e ↦
    if e ∈ M.pred S w then {row e (f e)} else {row e c, row e d}
  have hrows : ∀ e, ∀ g ∈ rows e, g x = ↑e := fun e g hg ↦ by
    simp only [rows] at hg
    split_ifs at hg <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg <;>
      rcases hg with rfl | rfl <;> exact update_single_apply_left hxy _ _
  have hres := restrict_iUnion_rows hrows
  have hne : ∀ e, (PluralAssign.restrict (⋃ e, rows e) x e).Nonempty := fun e ↦ by
    rw [hres]
    simp only [rows]
    split_ifs <;> simp
  have hsx : ∀ e, (PluralAssign.restrict (⋃ e, rows e) x e).value x = {e} := fun e ↦
    PluralAssign.value_restrict (hne e)
  have hsy : ∀ s ∈ M.pred S w,
      (PluralAssign.restrict (⋃ e, rows e) x s).value y = {f s} := fun s hs ↦ by
    rw [hres]
    simp [rows, hs, row]
  have hnsy : ¬ ∃ d, (PluralAssign.restrict (⋃ e, rows e) x e₀).value y = {d} := by
    rintro ⟨v, hv⟩
    rw [hres] at hv
    simp only [rows, he₀, ite_false] at hv
    have h1 := (PluralAssign.value_eq_singleton_iff.1 hv).2 (row e₀ c) (by simp) (by simp [row])
    have h2 := (PluralAssign.value_eq_singleton_iff.1 hv).2 (row e₀ d) (by simp) (by simp [row])
    simp only [row, PartialAssign.update_self] at h1 h2
    exact hcd (Flat.coe_inj.1 (h1.trans h2.symm))
  have hA : evalP M (.all x (.or (.not (.pred S x)) (.ex y (.and (.pred B y) (.rel Rd x y))))) w
      (⋃ e, rows e) = 1 := evalP_all_eq_true_iff.2 fun e ↦ ⟨hne e, by
    by_cases he : e ∈ M.pred S w
    · rw [evalP_or, evalP_not, evalP_pred_eq_true_iff.2 ⟨e, hsx e, he⟩, 
        SignType.joinMiddle_neg_one_left, evalP_ex_eq_true_iff, evalP_and,
        SignType.meetMiddle_eq_one_iff]
      exact ⟨evalP_pred_eq_true_iff.2 ⟨f e, hsy e he, (hf e he).1⟩,
        evalP_rel_eq_true_iff.2 ⟨e, f e, hsx e, hsy e he, (hf e he).2⟩⟩
    · rw [evalP_or, evalP_not, evalP_pred_eq_false_iff.2 ⟨e, hsx e, he⟩, neg_neg,
        SignType.joinMiddle_one_left]⟩
  have htaut : ∀ H : PluralAssign ℕ D,
      evalP M (.or (.valued y) (.not (.valued y))) w H = 1 := fun H ↦ by
    rw [evalP_or, evalP_not]
    by_cases h : ∃ d, H.value y = {d}
    · rw [evalP_valued_eq_true_iff.2 h]; rfl
    · rw [evalP_valued_eq_false_iff.2 h]; rfl
  have := hT (.or (.valued y) (.not (.valued y))) (w, ⋃ e, rows e) trivial
  simp only [Function.comp, evalP_and, hA, SignType.meetMiddle_one_left] at this
  rw [evalP_all_eq_false_iff.2 ⟨hne, e₀, by
      rw [evalP_and, evalP_valued_eq_false_iff.2 hnsy, SignType.meetMiddle_neg_one_left]⟩,
    evalP_all_eq_true_iff.2 fun e ↦ ⟨hne e, htaut _⟩] at this
  exact absurd this (by decide)

/-- *Every farmer who owns a donkey beats it* is weakly true at a world exactly when every farmer
who owns a donkey beats a donkey they own, the weak existential reading ((36), §6.7.1). -/
theorem trueAtP_donkey_iff [Nonempty D] (F Dn : P) (O Bt : R) (hxy : x ≠ y) :
    TrueAtP M (.all x (.or (.not (.and (.pred F x) (.ex y (.and (.pred Dn y) (.rel O x y)))))
      (.rel Bt x y))) w ↔
      ∀ a ∈ M.pred F w, (∃ d ∈ M.pred Dn w, (a, d) ∈ M.rel O w) →
        ∃ d ∈ M.pred Dn w, (a, d) ∈ M.rel O w ∧ (a, d) ∈ M.rel Bt w := by
  classical
  constructor
  · rintro ⟨G, hG⟩ a ha ⟨d₀, hd₀, hO₀⟩
    obtain ⟨hne, hZ⟩ := evalP_all_eq_true_iff.1 hG a
    have hsx : (G.restrict x a).value x = {a} := PluralAssign.value_restrict hne
    rw [evalP_or, evalP_not, evalP_and, evalP_pred_eq_true_iff.2 ⟨a, hsx, ha⟩,
      SignType.meetMiddle_one_left] at hZ
    cases hE : evalP M (.ex y (.and (.pred Dn y) (.rel O x y))) w (G.restrict x a) with
    | pos =>
      rw [hE, SignType.pos_eq_one, SignType.joinMiddle_neg_one_left] at hZ
      rw [SignType.pos_eq_one, evalP_ex_eq_true_iff, evalP_and,
        SignType.meetMiddle_eq_one_iff] at hE
      obtain ⟨b, hb, hDn⟩ := evalP_pred_eq_true_iff.1 hE.1
      obtain ⟨a₁, b₁, ha₁, hb₁, hO⟩ := evalP_rel_eq_true_iff.1 hE.2
      obtain ⟨a₂, b₂, ha₂, hb₂, hB⟩ := evalP_rel_eq_true_iff.1 hZ
      rw [← Set.singleton_injective (hsx.symm.trans ha₁),
        ← Set.singleton_injective (hb.symm.trans hb₁)] at hO
      rw [← Set.singleton_injective (hsx.symm.trans ha₂),
        ← Set.singleton_injective (hb.symm.trans hb₂)] at hB
      exact ⟨b, hDn, hO, hB⟩
    | neg =>
      obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 hE
      obtain ⟨hne', hfalse⟩ := hall d₀
      have hs1 := PluralAssign.value_restrict hne'
      have hs2 : ((G.restrict x a).restrict y d₀).value x = {a} := by
        obtain ⟨g, hg⟩ := hne'
        exact PluralAssign.value_eq_singleton_iff.2 ⟨⟨g, hg, (PluralAssign.mem_restrict.1 hg).1.2⟩,
          fun g' hg' _ ↦ (PluralAssign.mem_restrict.1 hg').1.2⟩
      rw [evalP_and, evalP_pred_eq_true_iff.2 ⟨d₀, hs1, hd₀⟩, SignType.meetMiddle_one_left,
        evalP_rel_eq_false_iff] at hfalse
      obtain ⟨a', b', ha', hb', hn⟩ := hfalse
      rw [← Set.singleton_injective (hs2.symm.trans ha'),
        ← Set.singleton_injective (hs1.symm.trans hb')] at hn
      exact absurd hO₀ hn
    | zero =>
      rw [hE, SignType.zero_eq_zero, SignType.neg_zero, SignType.joinMiddle_zero_left] at hZ
      exact absurd hZ (by decide)
  · intro h
    have h' : ∀ a, ∃ b, a ∈ M.pred F w → (∃ d ∈ M.pred Dn w, (a, d) ∈ M.rel O w) →
        b ∈ M.pred Dn w ∧ (a, b) ∈ M.rel O w ∧ (a, b) ∈ M.rel Bt w := fun a ↦ by
      by_cases ha : a ∈ M.pred F w
      · by_cases hd : ∃ d ∈ M.pred Dn w, (a, d) ∈ M.rel O w
        · obtain ⟨b, hb⟩ := h a ha hd
          exact ⟨b, fun _ _ ↦ hb⟩
        · exact ⟨Classical.arbitrary D, fun _ h ↦ absurd h hd⟩
      · exact ⟨Classical.arbitrary D, fun h ↦ absurd h ha⟩
    choose f hf using h'
    let row : D → D → PartialAssign ℕ D := fun e v ↦ (PartialAssign.single x e).update y v
    let rows : D → PluralAssign ℕ D := fun e ↦
      if e ∈ M.pred F w then
        if ∃ d ∈ M.pred Dn w, (e, d) ∈ M.rel O w then {row e (f e)} else Set.range (row e)
      else {PartialAssign.single x e}
    have hrows : ∀ e, ∀ g ∈ rows e, g x = ↑e := fun e g hg ↦ by
      simp only [rows] at hg
      split_ifs at hg
      · rw [Set.mem_singleton_iff.1 hg]; exact update_single_apply_left hxy _ _
      · obtain ⟨v, rfl⟩ := hg; exact update_single_apply_left hxy _ _
      · rw [Set.mem_singleton_iff.1 hg]; simp
    have hres := restrict_iUnion_rows hrows
    refine ⟨⋃ e, rows e, evalP_all_eq_true_iff.2 fun e ↦ ?_⟩
    have hne : (PluralAssign.restrict (⋃ e, rows e) x e).Nonempty := by
      rw [hres]
      simp only [rows]
      split_ifs <;> first | exact Set.singleton_nonempty _ | exact Set.range_nonempty _
    have hsx := PluralAssign.value_restrict hne
    refine ⟨hne, ?_⟩
    rw [evalP_or, evalP_not, evalP_and]
    by_cases he : e ∈ M.pred F w
    · rw [evalP_pred_eq_true_iff.2 ⟨e, hsx, he⟩, SignType.meetMiddle_one_left]
      by_cases hd : ∃ d ∈ M.pred Dn w, (e, d) ∈ M.rel O w
      · obtain ⟨hDn, hO, hB⟩ := hf e he hd
        have hsy : (PluralAssign.restrict (⋃ e, rows e) x e).value y = {f e} := by
          rw [hres]
          simp [rows, he, hd, row]
        rw [evalP_ex_eq_true_iff.2 (by
            rw [evalP_and, SignType.meetMiddle_eq_one_iff]
            exact ⟨evalP_pred_eq_true_iff.2 ⟨f e, hsy, hDn⟩,
              evalP_rel_eq_true_iff.2 ⟨e, f e, hsx, hsy, hO⟩⟩),
          SignType.joinMiddle_neg_one_left]
        exact evalP_rel_eq_true_iff.2 ⟨e, f e, hsx, hsy, hB⟩
      · have hE : evalP M (.ex y (.and (.pred Dn y) (.rel O x y))) w
            (PluralAssign.restrict (⋃ e, rows e) x e) = -1 := by
          rw [evalP_ex_eq_false_iff]
          refine ⟨?_, fun v ↦ ?_⟩
          · rw [evalP_and, Ne, SignType.meetMiddle_eq_one_iff]
            rintro ⟨h1, h2⟩
            obtain ⟨b, hb, hDnb⟩ := evalP_pred_eq_true_iff.1 h1
            obtain ⟨a₁, b₁, ha₁, hb₁, hO⟩ := evalP_rel_eq_true_iff.1 h2
            rw [← Set.singleton_injective (hsx.symm.trans ha₁),
              ← Set.singleton_injective (hb.symm.trans hb₁)] at hO
            exact hd ⟨b, hDnb, hO⟩
          · have hrv : (PluralAssign.restrict (⋃ e, rows e) x e).restrict y v = {row e v} := by
              rw [hres]
              simp only [rows, he, hd, ite_true, ite_false]
              ext g
              simp only [PluralAssign.mem_restrict, Set.mem_range, Set.mem_singleton_iff]
              constructor
              · rintro ⟨⟨v', rfl⟩, hv⟩
                simp only [row, PartialAssign.update_self] at hv
                rw [Flat.coe_inj.1 hv]
              · rintro rfl
                exact ⟨⟨v, rfl⟩, by simp [row]⟩
            rw [hrv]
            refine ⟨Set.singleton_nonempty _, ?_⟩
            have hsy : ({row e v} : PluralAssign ℕ D).value y = {v} := by simp [row]
            have hsx' : ({row e v} : PluralAssign ℕ D).value x = {e} := by
              simp [row, PartialAssign.update_of_ne hxy]
            rw [evalP_and]
            by_cases hv : v ∈ M.pred Dn w
            · rw [evalP_pred_eq_true_iff.2 ⟨v, hsy, hv⟩, SignType.meetMiddle_one_left]
              exact evalP_rel_eq_false_iff.2 ⟨e, v, hsx', hsy, fun hO ↦ hd ⟨v, hv, hO⟩⟩
            · rw [evalP_pred_eq_false_iff.2 ⟨v, hsy, hv⟩, SignType.meetMiddle_neg_one_left]
        rw [hE, neg_neg, SignType.joinMiddle_one_left]
    · rw [evalP_pred_eq_false_iff.2 ⟨e, hsx, he⟩, SignType.meetMiddle_neg_one_left,
        neg_neg, SignType.joinMiddle_one_left]

/-- The pronoun of the donkey sentence satisfies Transparency in every context ((37)–(38),
§6.7.2). -/
theorem felicitousP_donkey (C : Set (W × PluralAssign ℕ D)) (F Dn : P) (O Bt : R) (hxy : x ≠ y) :
    Felicitous (evalP M) C (.all x (.or (.not (.and (.pred F x)
        (.ex y (.and (.pred Dn y) (.rel O x y)))))
      (.rel Bt x y))) := by
  intro o ho
  simp [Formula.occurrences, hxy, hxy.symm] at ho
  subst ho
  intro φ p _
  simp only [Function.comp]
  refine evalP_all_congr fun a ↦ ?_
  rw [evalP_or, evalP_or, evalP_and]
  refine disj_transparency_parametric _ _ _ fun h ↦ ?_
  rw [evalP_not, SignType.neg_eq_neg_one_iff, evalP_and, SignType.meetMiddle_eq_one_iff,
    evalP_ex_eq_true_iff, evalP_and, SignType.meetMiddle_eq_one_iff] at h
  obtain ⟨b, hb, -⟩ := evalP_pred_eq_true_iff.1 h.2.1
  exact evalP_valued_eq_true_iff.2 ⟨_, hb⟩

/-- *It is not true that Sue has a donkey and that she beats it* is weakly true at a world
exactly when Sue has no donkey or has one she does not beat ((39)–(40)). Sue's owning and
beating are rendered as one-place predicates. -/
theorem trueAtP_not_ex_and_iff (Dk OS BS : P) :
    TrueAtP M (.not (.and (.ex x (.and (.pred Dk x) (.pred OS x))) (.pred BS x))) w ↔
      (∀ d, ¬ (d ∈ M.pred Dk w ∧ d ∈ M.pred OS w)) ∨
        ∃ d, d ∈ M.pred Dk w ∧ d ∈ M.pred OS w ∧ d ∉ M.pred BS w := by
  constructor
  · rintro ⟨G, hG⟩
    rw [evalP_not, SignType.neg_eq_one_iff, evalP_and] at hG
    cases hE : evalP M (.ex x (.and (.pred Dk x) (.pred OS x))) w G with
    | neg =>
      refine .inl fun d ⟨hDk, hOS⟩ ↦ ?_
      obtain ⟨-, hall⟩ := evalP_ex_eq_false_iff.1 hE
      obtain ⟨hne, hf⟩ := hall d
      have hs := PluralAssign.value_restrict hne
      rw [evalP_and, evalP_pred_eq_true_iff.2 ⟨d, hs, hDk⟩, SignType.meetMiddle_one_left,
        evalP_pred_eq_false_iff] at hf
      obtain ⟨d', hd', hn⟩ := hf
      rw [← Set.singleton_injective (hs.symm.trans hd')] at hn
      exact hn hOS
    | pos =>
      rw [hE, SignType.pos_eq_one, SignType.meetMiddle_one_left] at hG
      rw [SignType.pos_eq_one, evalP_ex_eq_true_iff, evalP_and,
        SignType.meetMiddle_eq_one_iff] at hE
      obtain ⟨d, hd, hDk⟩ := evalP_pred_eq_true_iff.1 hE.1
      obtain ⟨d₁, hd₁, hOS⟩ := evalP_pred_eq_true_iff.1 hE.2
      obtain ⟨d₂, hd₂, hBS⟩ := evalP_pred_eq_false_iff.1 hG
      rw [← Set.singleton_injective (hd.symm.trans hd₁)] at hOS
      rw [← Set.singleton_injective (hd.symm.trans hd₂)] at hBS
      exact .inr ⟨d, hDk, hOS, hBS⟩
    | zero =>
      rw [hE, SignType.zero_eq_zero, SignType.meetMiddle_zero_left] at hG
      exact absurd hG (by decide)
  · rintro (hnone | ⟨d, hDk, hOS, hBS⟩)
    · refine ⟨covering D x, ?_⟩
      rw [evalP_not, evalP_and, evalP_ex_eq_false_iff.2 ⟨?_, fun e ↦
        ⟨restrict_covering_nonempty x e, ?_⟩⟩, SignType.meetMiddle_neg_one_left]
      · rfl
      · rw [evalP_and, Ne, SignType.meetMiddle_eq_one_iff]
        rintro ⟨h1, h2⟩
        obtain ⟨d, hd, hDk⟩ := evalP_pred_eq_true_iff.1 h1
        obtain ⟨d', hd', hOS⟩ := evalP_pred_eq_true_iff.1 h2
        rw [← Set.singleton_injective (hd.symm.trans hd')] at hOS
        exact hnone d ⟨hDk, hOS⟩
      · have hs := PluralAssign.value_restrict (restrict_covering_nonempty x e)
        rw [evalP_and]
        by_cases he : e ∈ M.pred Dk w
        · rw [evalP_pred_eq_true_iff.2 ⟨e, hs, he⟩, SignType.meetMiddle_one_left]
          exact evalP_pred_eq_false_iff.2 ⟨e, hs, fun h ↦ hnone e ⟨he, h⟩⟩
        · rw [evalP_pred_eq_false_iff.2 ⟨e, hs, he⟩, SignType.meetMiddle_neg_one_left]
    · have hs : ({PartialAssign.single x d} : PluralAssign ℕ D).value x = {d} :=
        PluralAssign.value_singleton_eq_singleton_iff.2 (by simp)
      refine ⟨{PartialAssign.single x d}, ?_⟩
      rw [evalP_not, evalP_and, evalP_ex_eq_true_iff.2 (by
          rw [evalP_and, SignType.meetMiddle_eq_one_iff]
          exact ⟨evalP_pred_eq_true_iff.2 ⟨d, hs, hDk⟩, evalP_pred_eq_true_iff.2 ⟨d, hs, hOS⟩⟩),
        SignType.meetMiddle_one_left, evalP_pred_eq_false_iff.2 ⟨d, hs, hBS⟩]
      rfl

/-- Under Strong Truth, *there is a bathroom and it is upstairs* says that there is a bathroom
and every bathroom is upstairs ((47a)). -/
theorem stronglyTrueAt_ex_and_iff (B F : P) :
    StronglyTrueAt M (.and (.ex x (.pred B x)) (.pred F x)) w ↔
      (∃ d, d ∈ M.pred B w) ∧ ∀ d ∈ M.pred B w, d ∈ M.pred F w := by
  have hs : ∀ d : D, ({PartialAssign.single x d} : PluralAssign ℕ D).value x = {d} :=
    fun d ↦ PluralAssign.value_singleton_eq_singleton_iff.2 (by simp)
  constructor
  · rintro ⟨⟨G, hG⟩, hnf⟩
    rw [evalP_and, SignType.meetMiddle_eq_one_iff, evalP_ex_eq_true_iff] at hG
    obtain ⟨d, -, hd⟩ := evalP_pred_eq_true_iff.1 hG.1
    refine ⟨⟨d, hd⟩, fun d' hd' ↦ by_contra fun hn ↦ hnf {PartialAssign.single x d'} ?_⟩
    rw [evalP_and, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨d', hs d', hd'⟩),
      SignType.meetMiddle_one_left]
    exact evalP_pred_eq_false_iff.2 ⟨d', hs d', hn⟩
  · rintro ⟨⟨d, hd⟩, hall⟩
    refine ⟨⟨{PartialAssign.single x d}, ?_⟩, fun G hG ↦ ?_⟩
    · rw [evalP_and, evalP_ex_eq_true_iff.2 (evalP_pred_eq_true_iff.2 ⟨d, hs d, hd⟩),
        SignType.meetMiddle_one_left]
      exact evalP_pred_eq_true_iff.2 ⟨d, hs d, hall d hd⟩
    · rw [evalP_and] at hG
      cases hE : evalP M (.ex x (.pred B x)) w G with
      | neg =>
        obtain ⟨-, hf⟩ := evalP_ex_eq_false_iff.1 hE
        obtain ⟨d', hd', hn⟩ := evalP_pred_eq_false_iff.1 (hf d).2
        exact hn ((PluralAssign.value_restrict_eq_singleton_iff.1 hd').2 ▸ hd)
      | pos =>
        rw [hE, SignType.pos_eq_one, SignType.meetMiddle_one_left, evalP_pred_eq_false_iff] at hG
        obtain ⟨d', hd', hn⟩ := hG
        obtain ⟨d'', hd'', hB⟩ := evalP_pred_eq_true_iff.1 (evalP_ex_eq_true_iff.1 hE)
        rw [Set.singleton_injective (hd''.symm.trans hd')] at hB
        exact hn (hall d' hB)
      | zero =>
        rw [hE, SignType.zero_eq_zero, SignType.meetMiddle_zero_left] at hG
        exact absurd hG (by decide)

end Rows

end Spector2026
