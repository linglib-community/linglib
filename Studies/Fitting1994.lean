module

public import Mathlib.Order.Lattice
public import Linglib.Logic.Trivalent.Four
public import Linglib.Logic.Bilattice.Guard
public import Linglib.Core.Order.InvolutiveCompl

/-!
# Fitting (1994): Kleene's three valued logics and their children

Fitting shows that Kleene's strong three-valued logic is the consistent part `x ≤ₖ −x` of
Belnap's `FOUR`, and that the guard connective `P : Q`, which is `Q` if `P` is at least true and
`⊥` otherwise, extends Belnap's logic so that Kleene's weak logic and the asymmetric Lisp logic
become definable there (Definition 5.1). Both generalize to Ginsberg's product bilattices `L ⊙ L`,
where the guard is `⟨a, b⟩ : ⟨c, d⟩ = ⟨a ∧ c, a ∧ d⟩` (Definition 9.4).

The main results are the identities of Figure 4 for the guard, the closure theorems for exact
and consistent values (Theorems 9.2 and 9.3, `not_isExact_kTop`, `isConsistent_kSup`), the
identification of the Lisp and weak connectives on Kleene's values with `SignType.meetMiddle`
and `SignType.meetWeak`, and the collapse for bilinear bilattices: an equivalence of formulas
holds in `L ⊙ L` for a linear `L` iff it holds in `FOUR` (Theorem 10.5, `equivalent_iff_four`).

## Implementation notes

* The product, its negation and the conflation of §§6–7 are `Bilattice.Product` with its `Compl`
  and `Conflation` instances; a De Morgan lattice is a bounded distributive lattice with an
  `InvolutiveCompl`. §3's identification of
  Kleene's values with the consistent part of `FOUR` is `Trivalent.orderIsoConsistent`, and the
  closure clauses of Theorems 9.2 and 9.3 are `IsExact.inf`, `IsConsistent.compl` and their kin;
  the study keeps what the substrate lacks.
* The representation theorems of §8, with their negation- and conflation-preserving refinements
  (Theorems 8.2 and 8.3), and the tableau system of §4 are not formalized.
* Theorem 10.5 is stated for products of linear bounded lattices; `ofFour` embeds `FOUR` by
  sending the Boolean coordinates to the bounds, and `θ_⊤` reads it back.

## References

* [fitting-1994]
* [kleene-1952]
* [belnap-1977]
* [ginsberg-1988]
* [avron-1996]
* [peters-1979]
-/

@[expose] public section

open Bilattice Product SignType
open Bilattice.Product (guard)

namespace Fitting1994

/-! ### Formulas and the semantics behind the tableaux (§4) -/

/-- Formulas over the bilattice connectives, namely the truth connectives and negation, consensus
`⊓ₖ`, gullibility `⊔ₖ`, and the guard `P : Q` of §5. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | inf : Formula Atom → Formula Atom → Formula Atom
  | sup : Formula Atom → Formula Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | kInf : Formula Atom → Formula Atom → Formula Atom
  | kSup : Formula Atom → Formula Atom → Formula Atom
  | guard : Formula Atom → Formula Atom → Formula Atom

namespace Formula

variable {Atom L : Type*} [Lattice L]

/-- Evaluation in `L ⊙ L` under a valuation of the atoms (Definition 4.1). -/
def eval (v : Atom → L ⊙ L) : Formula Atom → L ⊙ L
  | atom a => v a
  | inf φ ψ => eval v φ ⊓ eval v ψ
  | sup φ ψ => eval v φ ⊔ eval v ψ
  | neg φ => (eval v φ)ᶜ
  | kInf φ ψ => eval v φ ⊓ₖ eval v ψ
  | kSup φ ψ => (eval v φ ⊔ₖ eval v ψ)
  | guard φ ψ => Product.guard (eval v φ) (eval v ψ)

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

-- §4
theorem restricts_iff_requires_neg (φ ψ : Formula Atom) :
    Restricts φ ψ ↔ Requires (.neg ψ) (.neg φ) := by
  have key : ∀ x y : FOUR, (x ≤ₖ FOUR.T → y ≤ₖ FOUR.T) ↔
      (FOUR.T ≤ₖ yᶜ → FOUR.T ≤ₖ xᶜ) := by decide
  exact forall_congr' fun v ↦ key _ _

-- §4
theorem equivalent_iff (φ ψ : Formula Atom) :
    Equivalent φ ψ ↔ Restricts φ ψ ∧ Requires φ ψ ∧ Restricts ψ φ ∧ Requires ψ φ := by
  have key : ∀ x y : FOUR, x = y ↔ (x ≤ₖ FOUR.T → y ≤ₖ FOUR.T) ∧ (FOUR.T ≤ₖ x → FOUR.T ≤ₖ y) ∧
      (y ≤ₖ FOUR.T → x ≤ₖ FOUR.T) ∧ (FOUR.T ≤ₖ y → FOUR.T ≤ₖ x) := by decide
  simp only [Equivalent, Restricts, Requires, key, forall_and]

end Formula

/-! ### The guard connective (§5) -/

theorem guard_four :
    ∀ x y : FOUR, guard x y = if FOUR.T ≤ₖ x then y else FOUR.U := by decide

section Guard

variable {L : Type*} [DistribLattice L] (x y z : L ⊙ L)

-- Figure 4
theorem guard_kInf_left :
    guard (x ⊓ₖ y) z = guard (x ⊓ y) z := by ext <;> simp [Product.guard]

-- Figure 4
theorem guard_kInf_left_eq :
    guard (x ⊓ₖ y) z = guard x z ⊓ₖ guard y z := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_kInf, con_kInf] <;>
    exact inf_inf_distrib_right _ _ _

-- Figure 4
theorem guard_kInf_left_eq_guard_guard :
    guard (x ⊓ₖ y) z = guard (guard x y) z := by
  ext <;> simp [Product.guard]

-- Figure 4
theorem guard_kInf_left_eq_guard_guard' :
    guard (x ⊓ₖ y) z = guard x (guard y z) := by
  ext <;> simp [Product.guard, inf_assoc]

-- Figure 4
theorem guard_kSup_left :
    guard (x ⊔ₖ y) z = guard (x ⊔ y) z := by ext <;> simp [Product.guard]

-- Figure 4
theorem guard_kSup_left_eq :
    guard (x ⊔ₖ y) z = guard x z ⊔ₖ guard y z := by
  ext <;> simp [Product.guard, inf_sup_right]

-- Figure 4
theorem guard_compl : guard x yᶜ = (guard x y)ᶜ := by
  ext <;> simp [Product.guard]

-- Figure 4
theorem guard_inf : guard x (y ⊓ z) = guard x y ⊓ guard x z := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_inf, con_inf]
  · exact inf_inf_distrib_left _ _ _
  · exact inf_sup_left _ _ _

-- Figure 4
theorem guard_sup : guard x (y ⊔ z) = guard x y ⊔ guard x z := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_sup, con_sup]
  · exact inf_sup_left _ _ _
  · exact inf_inf_distrib_left _ _ _

-- Figure 4
theorem guard_kInf : guard x (y ⊓ₖ z) = guard x y ⊓ₖ guard x z := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_kInf, con_kInf] <;>
    exact inf_inf_distrib_left _ _ _

-- Figure 4
theorem guard_kSup :
    guard x (y ⊔ₖ z) = guard x y ⊔ₖ guard x z := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_kSup, con_kSup] <;>
    exact inf_sup_left _ _ _

-- Figure 4
theorem kSup_guard_self : x ⊔ₖ guard y x = x := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_kSup, con_kSup] <;> rw [inf_comm] <;>
    exact sup_inf_self

-- Figure 4
theorem kInf_guard_self : x ⊓ₖ guard y x = guard y x := by
  ext <;> simp only [Product.guard, pro_mk, con_mk, pro_kInf, con_kInf] <;>
    rw [inf_comm y.pro, inf_left_idem]

variable {x y z}

theorem guard_le_guard_right (h : y ≤ z) : guard x y ≤ guard x z :=
  ⟨inf_le_inf_left _ h.1, inf_le_inf_left _ h.2⟩

theorem guard_kLE_guard_of_le (h : x ≤ y) : guard x z ≤ₖ guard y z :=
  ⟨inf_le_inf_right _ h.1, inf_le_inf_right _ h.1⟩

end Guard

theorem not_guard_le_guard_left :
    ¬ ∀ x y z : FOUR, x ≤ y → guard x z ≤ guard y z :=
  fun h ↦ absurd (h FOUR.U FOUR.T FOUR.F (by decide)) (by decide)

/-! ### Lisp and weak Kleene connectives through the guard (§5) -/

section Lisp

variable {L : Type*} [DistribLattice L]

/-- Lisp conjunction `P ∧⃗ Q = P ∧ (P : Q)` (Definition 5.1), which consults the second conjunct
only past the guard of the first. -/
def landL (x y : L ⊙ L) : L ⊙ L := x ⊓ guard x y

/-- Lisp disjunction `P ∨⃗ Q = P ∨ (¬P : Q)` (Definition 5.1). -/
def lorL (x y : L ⊙ L) : L ⊙ L := x ⊔ guard xᶜ y

/-- Weak Kleene conjunction `P ∧ʷ Q = (P ∧⃗ Q) ⊓ₖ (Q ∧⃗ P)` (Definition 5.1), the consensus of
the two evaluation orders. -/
def landW (x y : L ⊙ L) : L ⊙ L := landL x y ⊓ₖ landL y x

/-- Weak Kleene disjunction `P ∨ʷ Q = (P ∨⃗ Q) ⊓ₖ (Q ∨⃗ P)` (Definition 5.1). -/
def lorW (x y : L ⊙ L) : L ⊙ L := lorL x y ⊓ₖ lorL y x

variable (x y : L ⊙ L)

theorem inf_eq_landL_kSup_landL : x ⊓ y = landL x y ⊔ₖ landL y x := by
  ext
  · simp only [landL, Product.guard, pro_kSup, pro_inf, pro_mk]
    rw [inf_left_idem, inf_left_idem, inf_comm y.pro, sup_idem]
  · simp only [landL, Product.guard, con_kSup, con_inf, con_mk]
    exact le_antisymm (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
      (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right))
        (sup_le le_sup_right (inf_le_right.trans le_sup_left)))

theorem sup_eq_lorL_kSup_lorL : x ⊔ y = lorL x y ⊔ₖ lorL y x := by
  ext
  · simp only [lorL, Product.guard, pro_kSup, pro_sup, pro_mk, pro_compl]
    exact le_antisymm (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
      (sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right))
        (sup_le le_sup_right (inf_le_right.trans le_sup_left)))
  · simp only [lorL, Product.guard, con_kSup, con_sup, con_mk, pro_compl]
    rw [inf_left_idem, inf_left_idem, inf_comm y.con, sup_idem]

end Lisp

theorem landL_toFour : ∀ a b : SignType, landL (toFour a) (toFour b) =
    toFour (SignType.meetMiddle a b) := by decide

theorem lorL_toFour : ∀ a b : SignType, lorL (toFour a) (toFour b) =
    toFour (SignType.joinMiddle a b) := by decide

theorem landW_toFour : ∀ a b : SignType, landW (toFour a) (toFour b) =
    toFour (SignType.meetWeak a b) := by decide

theorem lorW_toFour : ∀ a b : SignType, lorW (toFour a) (toFour b) =
    toFour (SignType.joinWeak a b) := by decide

theorem meetMiddle_joinMiddle_distrib : ∀ a b c : SignType,
    SignType.meetMiddle a (SignType.joinMiddle b c) =
      SignType.joinMiddle (SignType.meetMiddle a b) (SignType.meetMiddle a c) := by
  decide

theorem not_landL_lorL_distrib :
    ¬ ∀ x y z : FOUR, landL x (lorL y z) = lorL (landL x y) (landL x z) :=
  fun h ↦ absurd (h FOUR.I FOUR.U FOUR.I) (by decide)

/-! ### Bilattices and the product construction (§§6–7) -/

section Product

variable {L : Type*} [Lattice L] [BoundedOrder L]

-- §6
theorem extremal :
    ((⊤ : L ⊙ L) ⊔ₖ ⊥) = mk ⊤ ⊤ ∧ (⊤ : L ⊙ L) ⊓ₖ ⊥ = mk ⊥ ⊥ ∧
      (mk ⊤ ⊤ : L ⊙ L) ⊓ mk ⊥ ⊥ = ⊥ ∧ (mk ⊤ ⊤ : L ⊙ L) ⊔ mk ⊥ ⊥ = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp

end Product

/-! ### Kleene's logics generalized (§9)

Definition 9.1's exact and consistent values are `IsExact` and `IsConsistent`, read off the
coordinates by `Product.isExact_iff` and `Product.isConsistent_iff`; their closure under the
truth connectives and negation (Theorems 9.2 and 9.3) is `IsExact.inf`, `IsExact.sup`,
`IsExact.compl`, `IsConsistent.inf`, `IsConsistent.sup` and `IsConsistent.compl`. The guard of
Definition 9.4 is `guard`, with its characterization in the bilattice operations
`guard_eq_kSup_compl`. -/

section Generalized

variable {L : Type*} [DistribLattice L] {x y z : L ⊙ L}

section Exact

variable [BoundedOrder L] [InvolutiveCompl L]

/-- The knowledge top `⊤ = (⊤, ⊤)` is not exact (Theorem 9.2). -/
theorem not_isExact_kTop [Nontrivial L] : ¬ IsExact (mk ⊤ ⊤ : L ⊙ L) := by
  rw [isExact_iff]
  simp

-- Theorem 9.2
theorem not_isExact_kBot [Nontrivial L] : ¬ IsExact (mk ⊥ ⊥ : L ⊙ L) := by
  rw [isExact_iff]
  simp

-- Theorem 9.2
theorem not_isExact_kInf [Nontrivial L] : ¬ IsExact ((⊤ : L ⊙ L) ⊓ₖ ⊥) := by
  rw [isExact_iff]
  simp

-- Theorem 9.2
theorem not_isExact_kSup [Nontrivial L] : ¬ IsExact ((⊤ : L ⊙ L) ⊔ₖ ⊥) := by
  rw [isExact_iff]
  simp

end Exact

section Consistent

variable [InvolutiveCompl L]

/-- The consistent values are closed under gullibility `⊔ₖ` below a common consistent upper bound
(Theorem 9.3). -/
theorem isConsistent_kSup (hx : IsConsistent x) (hy : IsConsistent y)
    (hz : IsConsistent z) (hxz : x ≤ₖ z) (hyz : y ≤ₖ z) : IsConsistent (x ⊔ₖ y) := by
  rw [isConsistent_iff] at *
  simp only [pro_kSup, con_kSup, InvolutiveCompl.compl_sup]
  exact sup_le (le_inf hx (hxz.2.trans (hz.trans (InvolutiveCompl.compl_le_compl hyz.1))))
    (le_inf (hyz.2.trans (hz.trans (InvolutiveCompl.compl_le_compl hxz.1))) hy)

-- §9
theorem isConsistent_guard (hy : IsConsistent y) (x : L ⊙ L) :
    IsConsistent (guard x y) := by
  rw [isConsistent_iff] at *
  simpa [Product.guard] using inf_le_right.trans (hy.trans le_sup_right)

end Consistent

variable {x' y' : L ⊙ L}

-- §9
theorem landL_kLE_landL (hx : x ≤ₖ x') (hy : y ≤ₖ y') : landL x y ≤ₖ landL x' y' :=
  ⟨inf_le_inf hx.1 (inf_le_inf hx.1 hy.1), sup_le_sup hx.2 (inf_le_inf hx.1 hy.2)⟩

-- §9
theorem lorL_kLE_lorL (hx : x ≤ₖ x') (hy : y ≤ₖ y') : lorL x y ≤ₖ lorL x' y' :=
  ⟨sup_le_sup hx.1 (inf_le_inf hx.2 hy.1), inf_le_inf hx.2 (inf_le_inf hx.2 hy.2)⟩

-- §9
theorem landW_kLE_landW (hx : x ≤ₖ x') (hy : y ≤ₖ y') : landW x y ≤ₖ landW x' y' :=
  ⟨inf_le_inf (landL_kLE_landL hx hy).1 (landL_kLE_landL hy hx).1,
    inf_le_inf (landL_kLE_landL hx hy).2 (landL_kLE_landL hy hx).2⟩

-- §9
theorem lorW_kLE_lorW (hx : x ≤ₖ x') (hy : y ≤ₖ y') : lorW x y ≤ₖ lorW x' y' :=
  ⟨inf_le_inf (lorL_kLE_lorL hx hy).1 (lorL_kLE_lorL hy hx).1,
    inf_le_inf (lorL_kLE_lorL hx hy).2 (lorL_kLE_lorL hy hx).2⟩

variable [InvolutiveCompl L]

-- §9
theorem isConsistent_landL (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (landL x y) :=
  hx.inf (isConsistent_guard hy x)

theorem isConsistent_lorL (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (lorL x y) :=
  hx.sup (isConsistent_guard hy xᶜ)

theorem isConsistent_landW (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (landW x y) :=
  (isConsistent_landL hx hy).kInf _

theorem isConsistent_lorW (hx : IsConsistent x) (hy : IsConsistent y) :
    IsConsistent (lorW x y) :=
  (isConsistent_lorL hx hy).kInf _

end Generalized

/-! ### Bilinear bilattices (§10) -/

/-- A bilattice is bilinear when any two members are comparable in at least one of the two
orders (Definition 10.1). -/
def Bilinear (B : Type*) [Preorder B] [Preorder (Know B)] : Prop :=
  ∀ x y : B, x ≤ y ∨ y ≤ x ∨ x ≤ₖ y ∨ y ≤ₖ x

-- Proposition 10.2
theorem bilinear_iff {L R : Type*} [PartialOrder L] [PartialOrder R] [BoundedOrder L]
    [BoundedOrder R] :
    Bilinear (L ⊙ R) ↔ (∀ a b : L, a ≤ b ∨ b ≤ a) ∧ ∀ a b : R, a ≤ b ∨ b ≤ a := by
  constructor
  · intro h
    refine ⟨fun a b ↦ ?_, fun a b ↦ ?_⟩
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
    rcases hL x.pro y.pro with h₁ | h₁ <;> rcases hR x.con y.con with h₂ | h₂
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

theorem theta_compl : theta a xᶜ = (theta a x)ᶜ := rfl

-- Lemma 10.4
theorem theta_inf : theta a (x ⊓ y) = theta a x ⊓ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_inf, con_inf, decide_inf, decide_sup]

theorem theta_sup : theta a (x ⊔ y) = theta a x ⊔ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_sup, con_sup, decide_inf, decide_sup]

theorem theta_kInf : theta a (x ⊓ₖ y) = theta a x ⊓ₖ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_kInf, con_kInf, decide_inf]

theorem theta_kSup : theta a (x ⊔ₖ y) = theta a x ⊔ₖ theta a y := by
  ext <;> simp only [theta, pro_mk, con_mk, pro_kSup, con_kSup, decide_sup]

theorem theta_guard :
    theta a (guard x y) = guard (theta a x) (theta a y) := by
  ext <;> simp only [theta, Product.guard, pro_mk, con_mk, decide_inf]

variable {Atom : Type*}

-- Lemma 10.4
theorem eval_theta (v : Atom → L ⊙ L) (φ : Formula Atom) :
    Formula.eval (theta a ∘ v) φ = theta a (Formula.eval v φ) := by
  induction φ with
  | atom _ => rfl
  | inf φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_inf]
  | sup φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_sup]
  | neg φ ih => simp only [Formula.eval, ih, theta_compl]
  | kInf φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_kInf]
  | kSup φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_kSup]
  | guard φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, theta_guard]

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

/-- An equivalence is valid in the bilinear product `L ⊙ L` iff it is valid in `FOUR`
(Theorem 10.5). -/
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

end Fitting1994
