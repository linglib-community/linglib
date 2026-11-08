module

public import Linglib.Logic.Trivalent.Four
public import Linglib.Logic.Bilattice.Guard
public import Linglib.Logic.Bilattice.Representation

/-!
# Fitting (1994): Kleene's three valued logics and their children

Kleene's strong three-valued logic is the consistent part of Belnap's `FOUR`. Fitting adds a guard
connective `P : Q`, which is `Q` when `P` is at least true and `⊥` otherwise, and with it defines
four-valued [Lisp](##landL_toFour) and [weak Kleene](##landW_toFour) connectives that agree with
the three-valued ones on Kleene's values. The guard and the new connectives make sense in any
bilattice with negation, where the consistent values stay [closed under them](##isConsistent_landW)
and, below a common consistent bound, [under gullibility](##isConsistent_kSup).
[An equivalence holds in a bilinear bilattice exactly when it holds in
`FOUR`](##Bilinear.equivalent_iff_four).

## Implementation notes

* Formulas are evaluated in any bilattice with negation; restriction, requirement and
  equivalence read them in `FOUR`. The tableaux are not formalized.
* Theorem 10.5 is proved as Fitting proves it: for a product `L ⊙ L` of a linear lattice, with
  `ofFour` embedding `FOUR` and `θ_⊤` reading it back, and then for any bilinear bilattice through
  the representation (`Bilattice.negProductIso`). Avron's representation needs only interlacing,
  where Fitting assumes distributivity, and the theorem assumes a nontrivial bilattice, since a
  one-element bilattice validates every equivalence.
* The Lisp and weak connectives are definitions on values whose formula counterparts evaluate to
  them by `rfl`, so the collapse covers Fitting's whole list of connectives.
* The guard is `Bilattice.guard`, defined by Fitting's characterization in the bilattice
  operations, so his product definition is its coordinate form. Its identities, those among the
  four bounds of an interlaced bilattice, the failure of the knowledge bounds to be exact, and the
  closure of the exact and consistent values under the truth operations and negation are
  substrate (`Bilattice.guard_compl`, `Bilattice.top_kInf_bot`,
  `Bilattice.not_isExact_ofKnow_top`, `Bilattice.IsConsistent.inf` and their kin).
* Fitting closes the consistent values under `⊕` for members with a common upper bound. The bound
  is read as consistent, and the members' consistency then follows from it.

## References

* [fitting-1994]
* [kleene-1952]
* [belnap-1977]
* [ginsberg-1988]
* [avron-1996]
* [peters-1979]
-/

@[expose] public section

open Bilattice Product Trivalent

namespace Fitting1994

/-! ### The guard connective -/

/-! The guard, its Figure 4 identities and its monotonicity are `Bilattice.guard` and its API. -/

-- §5, and p. 128: Definition 9.4 gives the §5 guard on `FOUR`
theorem guard_four :
    ∀ x y : FOUR, guard x y = if FOUR.T ≤ₖ x then y else FOUR.U := by decide

-- §5: but not in the first
theorem not_guard_le_guard_left :
    ¬ ∀ x y z : FOUR, x ≤ y → guard x z ≤ guard y z :=
  fun h ↦ absurd (h FOUR.U FOUR.T FOUR.F (by decide)) (by decide)

/-! ### Lisp and weak Kleene connectives through the guard -/

section Lisp

variable {B : Type*} [Lattice B] [Top B] [Compl B] [Lattice (Know B)]

/-- Lisp conjunction `P ∧⃗ Q = P ∧ (P : Q)` (Definition 5.1), which consults the second conjunct
only past the guard of the first. -/
def landL (x y : B) : B := x ⊓ guard x y

/-- Lisp disjunction `P ∨⃗ Q = P ∨ (¬P : Q)` (Definition 5.1). -/
def lorL (x y : B) : B := x ⊔ guard xᶜ y

/-- Weak Kleene conjunction `P ∧ʷ Q = (P ∧⃗ Q) ⊓ₖ (Q ∧⃗ P)` (Definition 5.1), the consensus of
the two evaluation orders. -/
def landW (x y : B) : B := landL x y ⊓ₖ landL y x

/-- Weak Kleene disjunction `P ∨ʷ Q = (P ∨⃗ Q) ⊓ₖ (Q ∨⃗ P)` (Definition 5.1). -/
def lorW (x y : B) : B := lorL x y ⊓ₖ lorL y x

end Lisp

section Strong

variable {L : Type*} [Lattice L] [BoundedOrder L] (x y : L ⊙ L)

-- p. 121: the strong connectives are the gullibility of the two evaluation orders
theorem inf_eq_landL_kSup_landL : x ⊓ y = landL x y ⊔ₖ landL y x := by
  ext <;> simp only [landL, pro_kSup, con_kSup, pro_inf, con_inf, pro_guard, con_guard]
  · rw [inf_left_idem, inf_left_idem, inf_comm y.pro, sup_idem]
  · rw [sup_sup_sup_comm, eq_comm, sup_eq_left]
    exact sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left)

theorem sup_eq_lorL_kSup_lorL : x ⊔ y = lorL x y ⊔ₖ lorL y x := by
  ext <;> simp only [lorL, pro_kSup, con_kSup, pro_sup, con_sup, pro_guard, con_guard, pro_compl]
  · rw [sup_sup_sup_comm, eq_comm, sup_eq_left]
    exact sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left)
  · rw [inf_left_idem, inf_left_idem, inf_comm y.con, sup_idem]

end Strong

/-- On Kleene's values the guarded conjunction is the Lisp conjunction, the Middle Kleene
`meetMiddle` (pp. 120–121). -/
theorem landL_toFour : ∀ a b : Trivalent, landL (toFour a) (toFour b) =
    toFour (Trivalent.meetMiddle a b) := by decide

-- pp. 120–121
theorem lorL_toFour : ∀ a b : Trivalent, lorL (toFour a) (toFour b) =
    toFour (Trivalent.joinMiddle a b) := by decide

/-- On Kleene's values the consensus of the two Lisp evaluation orders is Weak Kleene
conjunction (p. 121). -/
theorem landW_toFour : ∀ a b : Trivalent, landW (toFour a) (toFour b) =
    toFour (Trivalent.meetWeak a b) := by decide

-- p. 121
theorem lorW_toFour : ∀ a b : Trivalent, lorW (toFour a) (toFour b) =
    toFour (Trivalent.joinWeak a b) := by decide

-- p. 121: Lisp conjunction distributes over Lisp disjunction on Kleene's values
theorem meetMiddle_joinMiddle_distrib : ∀ a b c : Trivalent,
    Trivalent.meetMiddle a (Trivalent.joinMiddle b c) =
      Trivalent.joinMiddle (Trivalent.meetMiddle a b) (Trivalent.meetMiddle a c) := by
  decide

-- p. 121: but not on `FOUR`, with `P = R = ⊤` and `Q = ⊥`
theorem not_landL_lorL_distrib :
    ¬ ∀ x y z : FOUR, landL x (lorL y z) = lorL (landL x y) (landL x z) :=
  fun h ↦ absurd (h FOUR.I FOUR.U FOUR.I) (by decide)

/-! ### Formulas, restriction and requirement -/

/-- Formulas over the bilattice connectives, namely the truth connectives and negation, consensus
`⊓ₖ`, gullibility `⊔ₖ`, and the guard `P : Q`. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | inf : Formula Atom → Formula Atom → Formula Atom
  | sup : Formula Atom → Formula Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | kInf : Formula Atom → Formula Atom → Formula Atom
  | kSup : Formula Atom → Formula Atom → Formula Atom
  | guard : Formula Atom → Formula Atom → Formula Atom

namespace Formula

variable {Atom B : Type*} [Lattice B] [Top B] [Compl B] [Lattice (Know B)]

/-- Evaluation in a bilattice under a valuation of the atoms, extended inductively
(Definition 4.1, there in `FOUR`; p. 129 for any bilattice). -/
def eval (v : Atom → B) : Formula Atom → B
  | atom a => v a
  | inf φ ψ => eval v φ ⊓ eval v ψ
  | sup φ ψ => eval v φ ⊔ eval v ψ
  | neg φ => (eval v φ)ᶜ
  | kInf φ ψ => eval v φ ⊓ₖ eval v ψ
  | kSup φ ψ => (eval v φ ⊔ₖ eval v ψ)
  | guard φ ψ => Bilattice.guard (eval v φ) (eval v ψ)

/-- Lisp conjunction of formulas (Definition 5.1). -/
def landL (φ ψ : Formula Atom) : Formula Atom := .inf φ (.guard φ ψ)

/-- Lisp disjunction of formulas (Definition 5.1). -/
def lorL (φ ψ : Formula Atom) : Formula Atom := .sup φ (.guard (.neg φ) ψ)

/-- Weak Kleene conjunction of formulas (Definition 5.1). -/
def landW (φ ψ : Formula Atom) : Formula Atom := .kInf (landL φ ψ) (landL ψ φ)

/-- Weak Kleene disjunction of formulas (Definition 5.1). -/
def lorW (φ ψ : Formula Atom) : Formula Atom := .kInf (lorL φ ψ) (lorL ψ φ)

variable (v : Atom → B) (φ ψ : Formula Atom)

@[simp] theorem eval_landL : eval v (landL φ ψ) = Fitting1994.landL (eval v φ) (eval v ψ) := rfl
@[simp] theorem eval_lorL : eval v (lorL φ ψ) = Fitting1994.lorL (eval v φ) (eval v ψ) := rfl
@[simp] theorem eval_landW : eval v (landW φ ψ) = Fitting1994.landW (eval v φ) (eval v ψ) := rfl
@[simp] theorem eval_lorW : eval v (lorW φ ψ) = Fitting1994.lorW (eval v φ) (eval v ψ) := rfl

theorem eval_comp {C : Type*} [Lattice C] [Top C] [Compl C] [Lattice (Know C)] (f : B → C)
    (hinf : ∀ x y, f (x ⊓ y) = f x ⊓ f y) (hsup : ∀ x y, f (x ⊔ y) = f x ⊔ f y)
    (hcompl : ∀ x, f xᶜ = (f x)ᶜ) (hkInf : ∀ x y, f (x ⊓ₖ y) = f x ⊓ₖ f y)
    (hkSup : ∀ x y, f (x ⊔ₖ y) = f x ⊔ₖ f y)
    (hguard : ∀ x y, f (Bilattice.guard x y) = Bilattice.guard (f x) (f y)) :
    eval (f ∘ v) φ = f (eval v φ) := by
  induction φ with
  | atom _ => rfl
  | inf φ ψ ihφ ihψ => simp only [eval, ihφ, ihψ, hinf]
  | sup φ ψ ihφ ihψ => simp only [eval, ihφ, ihψ, hsup]
  | neg φ ih => simp only [eval, ih, hcompl]
  | kInf φ ψ ihφ ihψ => simp only [eval, ihφ, ihψ, hkInf]
  | kSup φ ψ ihφ ihψ => simp only [eval, ihφ, ihψ, hkSup]
  | guard φ ψ ihφ ihψ => simp only [eval, ihφ, ihψ, hguard]

/-- `X` restricts `Y` when, under every valuation in `FOUR`, `Y` is at most true (`⊥` or `true`)
whenever `X` is (Definition 4.2). -/
def Restricts (φ ψ : Formula Atom) : Prop :=
  ∀ v : Atom → FOUR, eval v φ ≤ₖ FOUR.T → eval v ψ ≤ₖ FOUR.T

/-- `X` requires `Y` when, under every valuation in `FOUR`, `Y` is at least true (`true` or `⊤`)
whenever `X` is (Definition 4.2). -/
def Requires (φ ψ : Formula Atom) : Prop :=
  ∀ v : Atom → FOUR, FOUR.T ≤ₖ eval v φ → FOUR.T ≤ₖ eval v ψ

/-- `X ≡ Y` when the two formulas take the same value in `FOUR` under every valuation. -/
def Equivalent (φ ψ : Formula Atom) : Prop := ∀ v : Atom → FOUR, eval v φ = eval v ψ

-- p. 118
theorem restricts_iff_requires_neg : Restricts φ ψ ↔ Requires (.neg ψ) (.neg φ) := by
  have key : ∀ x y : FOUR, (x ≤ₖ FOUR.T → y ≤ₖ FOUR.T) ↔
      (FOUR.T ≤ₖ yᶜ → FOUR.T ≤ₖ xᶜ) := by decide
  exact forall_congr' fun v ↦ key _ _

-- Proposition 4.4(3)
theorem equivalent_iff :
    Equivalent φ ψ ↔ Restricts φ ψ ∧ Requires φ ψ ∧ Restricts ψ φ ∧ Requires ψ φ := by
  have key : ∀ x y : FOUR, x = y ↔ (x ≤ₖ FOUR.T → y ≤ₖ FOUR.T) ∧ (FOUR.T ≤ₖ x → FOUR.T ≤ₖ y) ∧
      (y ≤ₖ FOUR.T → x ≤ₖ FOUR.T) ∧ (FOUR.T ≤ₖ y → FOUR.T ≤ₖ x) := by decide
  simp only [Equivalent, Restricts, Requires, key, forall_and]

/-! Fitting's tableaux for the Lisp distributive law (Figure 8): the left side requires the right,
and the valuation read off the open middle branch shows the converse fails (p. 122). -/

theorem requires_landL_lorL (φ ψ χ : Formula Atom) :
    Requires (φ.landL (ψ.lorL χ)) ((φ.landL ψ).lorL (φ.landL χ)) := by
  have key : ∀ p q r : FOUR, FOUR.T ≤ₖ Fitting1994.landL p (Fitting1994.lorL q r) →
      FOUR.T ≤ₖ Fitting1994.lorL (Fitting1994.landL p q) (Fitting1994.landL p r) := by decide
  exact fun v ↦ key _ _ _

theorem not_requires_lorL_landL {p q r : Atom} (hpq : p ≠ q) (hrq : r ≠ q) :
    ¬ Requires (((atom p).landL (atom q)).lorL ((atom p).landL (atom r)))
      ((atom p).landL ((atom q).lorL (atom r))) := by
  classical
  intro h
  have := h (Function.update (fun _ ↦ FOUR.I) q FOUR.U)
  simp only [eval_landL, eval_lorL, eval, Function.update_self, Function.update_of_ne hpq,
    Function.update_of_ne hrq] at this
  exact absurd (this (by decide)) (by decide)

end Formula

/-! ### Kleene's logics generalized -/

section Generalized

variable {B : Type*}

-- Theorem 9.2: the exact values are not closed under `⊗`
theorem exists_not_isExact_kInf [Lattice B] [BoundedOrder B] [Lattice (Know B)]
    [BoundedOrder (Know B)] [IsInterlaced B] [InvolutiveCompl (Know B)] [Conflation B]
    (h : (⊥ : Know B) ≠ ⊤) :
    ∃ x y : B, IsExact x ∧ IsExact y ∧ ¬ IsExact (x ⊓ₖ y) :=
  ⟨⊤, ⊥, conf_top, conf_bot, top_kInf_bot (B := B) ▸ not_isExact_ofKnow_bot h⟩

-- Theorem 9.2: nor under `⊕`
theorem exists_not_isExact_kSup [Lattice B] [BoundedOrder B] [Lattice (Know B)]
    [BoundedOrder (Know B)] [IsInterlaced B] [InvolutiveCompl (Know B)] [Conflation B]
    (h : (⊥ : Know B) ≠ ⊤) :
    ∃ x y : B, IsExact x ∧ IsExact y ∧ ¬ IsExact (x ⊔ₖ y) :=
  ⟨⊤, ⊥, conf_top, conf_bot, top_kSup_bot (B := B) ▸ not_isExact_ofKnow_top h⟩

/-- Two values below a common consistent value have a consistent gullibility (Theorem 9.3). The
bound alone suffices: consistency passes down the knowledge order. -/
theorem isConsistent_kSup [Lattice (Know B)] [InvolutiveCompl (Know B)] {x y z : B}
    (hz : IsConsistent z) (hxz : x ≤ₖ z) (hyz : y ≤ₖ z) : IsConsistent (x ⊔ₖ y) :=
  hz.anti (sup_le (α := Know B) hxz hyz)

section Lisp

variable [Lattice B] [Top B] [Compl B] [Lattice (Know B)] [IsInterlaced B] {x y x' y' : B}

/-! The Lisp and weak connectives are knowledge-monotone by the monotonicity of the guard and
interlacing (p. 128). -/

variable [Negation B] in
theorem landL_kLE_landL (hx : x ≤ₖ x') (hy : y ≤ₖ y') : landL x y ≤ₖ landL x' y' :=
  inf_kLE_inf hx (guard_kLE_guard hx hy)

variable [Negation B] in
theorem lorL_kLE_lorL (hx : x ≤ₖ x') (hy : y ≤ₖ y') : lorL x y ≤ₖ lorL x' y' :=
  sup_kLE_sup hx (guard_kLE_guard (compl_kLE_compl hx) hy)

variable [Negation B] in
theorem landW_kLE_landW (hx : x ≤ₖ x') (hy : y ≤ₖ y') : landW x y ≤ₖ landW x' y' :=
  inf_le_inf (α := Know B) (landL_kLE_landL hx hy) (landL_kLE_landL hy hx)

variable [Negation B] in
theorem lorW_kLE_lorW (hx : x ≤ₖ x') (hy : y ≤ₖ y') : lorW x y ≤ₖ lorW x' y' :=
  inf_le_inf (α := Know B) (lorL_kLE_lorL hx hy) (lorL_kLE_lorL hy hx)

variable [InvolutiveCompl (Know B)] [Conflation B]

/-! The consistent values are closed under the Lisp and weak connectives (p. 128). -/

theorem isConsistent_landL (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (landL x y) :=
  hx.inf (hy.guard x)

theorem isConsistent_lorL (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (lorL x y) :=
  hx.sup (hy.guard xᶜ)

/-- The consistent values of a bilattice are closed under weak Kleene conjunction, so the weak
logic generalizes with Kleene's values as its consistent part (p. 128). -/
theorem isConsistent_landW (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (landW x y) :=
  (isConsistent_landL hx hy).kInf _

theorem isConsistent_lorW (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (lorW x y) :=
  (isConsistent_lorL hx hy).kInf _

end Lisp

end Generalized

/-! ### Bilinear bilattices -/

/-- A bilattice is bilinear when any two members are comparable in at least one of the two
orders (Definition 10.1). -/
def Bilinear (B : Type*) [Preorder B] [Preorder (Know B)] : Prop :=
  ∀ x y : B, x ≤ y ∨ y ≤ x ∨ x ≤ₖ y ∨ y ≤ₖ x

-- Proposition 10.2
theorem bilinear_iff {L R : Type*} [PartialOrder L] [PartialOrder R] [BoundedOrder L]
    [BoundedOrder R] :
    Bilinear (L ⊙ R) ↔ Std.Total (α := L) (· ≤ ·) ∧ Std.Total (α := R) (· ≤ ·) := by
  constructor
  · intro h
    refine ⟨⟨fun a b ↦ ?_⟩, ⟨fun a b ↦ ?_⟩⟩
    · rcases h (mk a ⊥) (mk b ⊥) with h | h | h | h
      · exact .inl h.1
      · exact .inr h.1
      · exact .inl h.1
      · exact .inr h.1
    · rcases h (mk ⊥ a) (mk ⊥ b) with h | h | h | h
      · exact .inr h.2
      · exact .inl h.2
      · exact .inl h.2
      · exact .inr h.2
  · rintro ⟨hL, hR⟩ x y
    rcases hL.total x.pro y.pro with h₁ | h₁ <;> rcases hR.total x.con y.con with h₂ | h₂
    · exact .inr (.inr (.inl ⟨h₁, h₂⟩))
    · exact .inl ⟨h₁, h₂⟩
    · exact .inr (.inl ⟨h₁, h₂⟩)
    · exact .inr (.inr (.inr ⟨h₁, h₂⟩))

section Theta

variable {L : Type*} [LinearOrder L] (a : L)

/-- `θ_a` reads a member of `L ⊙ L` into `FOUR` coordinatewise by `a → x`, which is `true` iff
`a ≤ x` (Definition 10.3). -/
def theta (x : L ⊙ L) : FOUR := mk (decide (a ≤ x.pro)) (decide (a ≤ x.con))

variable (x y : L ⊙ L)

private theorem decide_inf (p q : L) : decide (a ≤ p ⊓ q) = (decide (a ≤ p) ⊓ decide (a ≤ q)) := by
  by_cases hp : a ≤ p <;> by_cases hq : a ≤ q <;> simp [hp, hq]

private theorem decide_sup (p q : L) : decide (a ≤ p ⊔ q) = (decide (a ≤ p) ⊔ decide (a ≤ q)) := by
  by_cases hp : a ≤ p <;> by_cases hq : a ≤ q <;> simp [hp, hq]

-- Lemma 10.4
theorem theta_compl : theta a xᶜ = (theta a x)ᶜ := rfl

theorem theta_inf : theta a (x ⊓ y) = theta a x ⊓ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_inf, con_inf, decide_inf, decide_sup]

theorem theta_sup : theta a (x ⊔ y) = theta a x ⊔ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_sup, con_sup, decide_inf, decide_sup]

theorem theta_kInf : theta a (x ⊓ₖ y) = theta a x ⊓ₖ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_kInf, con_kInf, decide_inf]

theorem theta_kSup : theta a (x ⊔ₖ y) = theta a x ⊔ₖ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_kSup, con_kSup, decide_sup]

theorem theta_guard [BoundedOrder L] :
    theta a (guard x y) = guard (theta a x) (theta a y) := by
  ext <;> simp only [theta, pro_guard, con_guard, pro_mk, con_mk, decide_inf]

variable {Atom : Type*}

-- Lemma 10.4
theorem eval_theta [BoundedOrder L] (v : Atom → L ⊙ L) (φ : Formula Atom) :
    Formula.eval (theta a ∘ v) φ = theta a (Formula.eval v φ) :=
  Formula.eval_comp v φ _ (theta_inf a) (theta_sup a) (theta_compl a) (theta_kInf a)
    (theta_kSup a) fun x y ↦ theta_guard a x y

variable {a x y}

private theorem decide_ne {p q : L} (h : p ≠ q) : decide (p ⊔ q ≤ p) ≠ decide (p ⊔ q ≤ q) := by
  intro heq
  rw [decide_eq_decide, sup_le_iff, sup_le_iff, and_iff_right le_rfl, and_iff_left le_rfl] at heq
  rcases le_total p q with hle | hle
  · exact h (hle.antisymm (heq.2 hle))
  · exact h ((heq.1 hle).antisymm hle)

-- Theorem 10.5
theorem exists_theta_ne (h : x ≠ y) : ∃ a, theta a x ≠ theta a y := by
  by_cases hp : x.pro = y.pro
  · have hc : x.con ≠ y.con := fun hc ↦ h (Product.ext hp hc)
    exact ⟨x.con ⊔ y.con, fun heq ↦ decide_ne hc (congrArg con heq)⟩
  · exact ⟨x.pro ⊔ y.pro, fun heq ↦ decide_ne hp (congrArg pro heq)⟩

variable [BoundedOrder L]

/-- The embedding of `FOUR` into `L ⊙ L` sends the Boolean coordinates to the bounds. -/
def ofFour (z : FOUR) : L ⊙ L := mk (if z.pro then ⊤ else ⊥) (if z.con then ⊤ else ⊥)

theorem theta_top_ofFour [Nontrivial L] (z : FOUR) : theta (⊤ : L) (ofFour z) = z := by
  ext
  · show decide ((⊤ : L) ≤ if z.pro then ⊤ else ⊥) = z.pro
    cases z.pro <;> simp
  · show decide ((⊤ : L) ≤ if z.con then ⊤ else ⊥) = z.con
    cases z.con <;> simp

-- Theorem 10.5 for the products `L ⊙ L` of a linear `L`
theorem equivalent_iff_four [Nontrivial L] (φ ψ : Formula Atom) :
    (∀ v : Atom → L ⊙ L, Formula.eval v φ = Formula.eval v ψ) ↔ Formula.Equivalent φ ψ := by
  constructor
  · intro h v
    have hv : theta (⊤ : L) ∘ (ofFour ∘ v) = v := funext fun b ↦ theta_top_ofFour (v b)
    calc Formula.eval v φ = Formula.eval (theta (⊤ : L) ∘ (ofFour ∘ v)) φ := by rw [hv]
      _ = theta (⊤ : L) (Formula.eval (ofFour ∘ v) φ) := eval_theta _ _ _
      _ = theta (⊤ : L) (Formula.eval (ofFour ∘ v) ψ) := by rw [h]
      _ = Formula.eval (theta (⊤ : L) ∘ (ofFour ∘ v)) ψ := (eval_theta _ _ _).symm
      _ = Formula.eval v ψ := by rw [hv]
  · intro h v
    by_contra hne
    obtain ⟨a, ha⟩ := exists_theta_ne hne
    exact ha (by rw [← eval_theta, ← eval_theta, h])

end Theta

/-! ### Bilinear bilattices through the representation

Fitting proves Theorem 10.5 for a distributive bilattice by representing it as `L ⊙ L`; Avron's
representation of interlaced bilattices with negation (`Bilattice.negProductIso`) lets the same
argument run for any interlaced one. -/

section Representation

variable {B Atom : Type*} [Lattice B] [Lattice (Know B)] [IsInterlaced B] [BoundedOrder (Know B)]

-- Proposition 10.2
theorem Bilinear.total_Ici (hB : Bilinear B) : Std.Total (α := Set.Ici (ofKnow ⊥ : B)) (· ≤ ·) where
  total a b := by
    rcases hB a b with h | h | h | h
    · exact .inl h
    · exact .inr h
    · exact .inl ((kLE_iff_le_of_ofKnow_bot_le a.2 b.2).1 h)
    · exact .inr ((kLE_iff_le_of_ofKnow_bot_le b.2 a.2).1 h)

variable [BoundedOrder B] [InvolutiveCompl B] [Negation B]

theorem eval_negProductIso (v : Atom → B) (φ : Formula Atom) :
    Formula.eval (negProductIso ∘ v) φ = negProductIso (Formula.eval v φ) :=
  have hkInf := map_kInf_of_kLE_iff negProductIso negProductIso_kLE_iff
  have hkSup := map_kSup_of_kLE_iff negProductIso negProductIso_kLE_iff
  Formula.eval_comp v φ _ negProductIso.map_inf negProductIso.map_sup negProductIso_compl hkInf
    hkSup fun x y ↦ by
      simp only [Bilattice.guard, hkInf, hkSup, negProductIso_compl, OrderIso.map_top]

/-- An equivalence is valid in a nontrivial bilinear interlaced bilattice with negation iff it is
valid in `FOUR`, so bilinear bilattices validate no new equivalences (Theorem 10.5). -/
theorem Bilinear.equivalent_iff_four [Nontrivial B] (hB : Bilinear B) (φ ψ : Formula Atom) :
    (∀ v : Atom → B, Formula.eval v φ = Formula.eval v ψ) ↔ Formula.Equivalent φ ψ := by
  classical
  have := hB.total_Ici
  let _ : LinearOrder (Set.Ici (ofKnow ⊥ : B)) := Lattice.toLinearOrder _
  have : Nontrivial (Set.Ici (ofKnow ⊥ : B)) := not_subsingleton_iff_nontrivial.1 fun _ ↦
    let ⟨_, _, hxy⟩ := exists_pair_ne B
    hxy (negProductIso.injective (Product.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))
  rw [← Fitting1994.equivalent_iff_four (L := Set.Ici (ofKnow ⊥ : B))]
  refine ⟨fun h w ↦ ?_, fun h v ↦ negProductIso.injective ?_⟩
  · have hw : negProductIso ∘ (negProductIso.symm ∘ w) = w :=
      funext fun _ ↦ negProductIso.apply_symm_apply _
    rw [← hw, eval_negProductIso, eval_negProductIso, h]
  · rw [← eval_negProductIso, ← eval_negProductIso, h]

end Representation

end Fitting1994
