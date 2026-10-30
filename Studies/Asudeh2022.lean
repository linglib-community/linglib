module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.List.Count
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Logic.Equiv.Defs
public import Linglib.Data.Examples.Asudeh2022
public import Linglib.Semantics.Quantification.Polyadic
public import Studies.HeimKratzer1998
public import Studies.BresnanEtAl1982
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.BigOperators.Fin
public import Linglib.Data.Examples.Readers

/-!
# Asudeh (2022): Glue Semantics

In Glue Semantics a word contributes *meaning constructors*, lambda terms paired with formulas
of the implicational fragment of linear logic, and a sentence means what a proof of its clause
from these premises computes, implication elimination being function application and
introduction abstraction. Linear logic lacks weakening and contraction, so a proof uses each
premise exactly once, but keeps commutativity, so word order does not constrain composition.
Asudeh's examples follow: Finnish *Join vettä* and English *I drank water* spread the same three
premises over two and three words, and *Everybody loves somebody* has one syntactic structure
but two proofs, one per scope reading. Asudeh also takes resource sensitivity to do the work of
LFG's Completeness and Coherence, which the Dutch cross-serial clauses of Bresnan, Kaplan, Peters
and Zaenen bear out.

## Implementation notes

* Proofs are intrinsically typed λ-terms over a list of premises; the structural rules rename
  premise positions, and `Term.Linear` counts uses.
* The quantifiers' scope variable `∀S` is instantiated to the clause, as in the paper's proofs.
* A Dutch control verb takes its complement as a property, so the object it shares is used twice
  only in the meaning.
* Proof nets use Danos and Regnier's criterion on mathlib's `SimpleGraph.IsTree`.

## TODO

* Prove `derivable_iff_exists_correct`, by desequentialization and sequentialization, and
  define the net of a linear term, so that `card_correct_loves` counts proofs up to βη.
* Planarity of linkings characterizes the Lambek calculus, but stating it needs directional
  types, which Glue's `⊸` lacks.

## References

* [asudeh-2022]
* [girard-1987]
* [klein-sag-1985]
* [kaplan-bresnan-1982]
* [danos-regnier-1989]
* [bresnan-etal-1982]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Asudeh2022

open Quantifier
open Quantifier.Det (every)
open Quantifier.Polyadic (surfaceScope inverseScope)

/-! ### Proofs as linear terms -/

/-- Formulas of the implicational fragment of linear logic over instantiated atoms. -/
inductive GlueTy (α : Type*)
  | atom (a : α)
  | lolli (A B : GlueTy α)
  deriving DecidableEq, Repr

infixr:25 " ⊸ " => GlueTy.lolli

variable {α : Type*}

/-- A proof from a list of premises, as a λ-term. A variable names a position of the list,
    application is implication elimination, and abstraction discharges a hypothesis appended to
    the list. -/
inductive Term : List (GlueTy α) → GlueTy α → Type _
  | var {Γ : List (GlueTy α)} (n : ℕ) {T : GlueTy α} (h : Γ[n]? = some T) : Term Γ T
  | app {Γ : List (GlueTy α)} {A B : GlueTy α} : Term Γ (A ⊸ B) → Term Γ A → Term Γ B
  | lam {Γ : List (GlueTy α)} (A : GlueTy α) {B : GlueTy α} : Term (Γ ++ [A]) B → Term Γ (A ⊸ B)

/-- The positions a proof uses, with repetition. -/
def Term.uses {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → List ℕ
  | .var n _ => [n]
  | .app f a => f.uses ++ a.uses
  | .lam _ b => b.uses

/-- Every hypothesis is used exactly once. -/
def Term.HypLinear {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → Prop
  | .var _ _ => True
  | .app f a => f.HypLinear ∧ a.HypLinear
  | .lam _ b => b.uses.count Γ.length = 1 ∧ b.HypLinear

instance Term.decHypLinear {Γ : List (GlueTy α)} {T : GlueTy α} :
    (t : Term Γ T) → Decidable t.HypLinear
  | .var _ _ => isTrue trivial
  | .app f a => @instDecidableAnd _ _ (decHypLinear f) (decHypLinear a)
  | .lam _ b => @instDecidableAnd _ _ inferInstance (decHypLinear b)

/-- A proof is linear if it uses every premise and every hypothesis exactly once. -/
def Term.Linear {Γ : List (GlueTy α)} {T : GlueTy α} (t : Term Γ T) : Prop :=
  (∀ i < Γ.length, t.uses.count i = 1) ∧ t.HypLinear

instance {Γ : List (GlueTy α)} {T : GlueTy α} (t : Term Γ T) : Decidable t.Linear :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Curry–Howard evaluation -/

variable (D : α → Type)

/-- The type of meanings a formula pairs with. -/
def GlueTy.denote : GlueTy α → Type
  | .atom a => D a
  | .lolli A B => A.denote → B.denote

/-- Meanings for the premises of a list. -/
inductive Env : List (GlueTy α) → Type _
  | nil : Env []
  | cons {T : GlueTy α} {Γ : List (GlueTy α)} : T.denote D → Env Γ → Env (T :: Γ)

variable {D}

/-- The meaning at a position. -/
def Env.get : {Γ : List (GlueTy α)} → Env D Γ → (n : ℕ) → {T : GlueTy α} →
    Γ[n]? = some T → T.denote D
  | _, .cons v _, 0, _, h => (Option.some.inj h) ▸ v
  | _, .cons _ ρ, n + 1, _, h => ρ.get n h

/-- The meanings extended by one, for a hypothesis. -/
def Env.snoc {T : GlueTy α} : {Γ : List (GlueTy α)} → Env D Γ → T.denote D → Env D (Γ ++ [T])
  | _, .nil, v => .cons v .nil
  | _, .cons u ρ, v => .cons u (ρ.snoc v)

theorem Env.get_congr {Γ : List (GlueTy α)} (ρ : Env D Γ) {n m : ℕ} {T : GlueTy α} (e : n = m)
    (h : Γ[n]? = some T) (h' : Γ[m]? = some T) : ρ.get n h = ρ.get m h' := by
  subst e; rfl

theorem Env.get_snoc_of_lt {A B : GlueTy α} : ∀ {Γ : List (GlueTy α)} (ρ : Env D Γ)
    (v : A.denote D) {n : ℕ} (_ : n < Γ.length) (h : (Γ ++ [A])[n]? = some B)
    (h' : Γ[n]? = some B), (ρ.snoc v).get n h = ρ.get n h'
  | _, .cons _ _, _, 0, _, _, _ => rfl
  | _, .cons _ ρ, v, n + 1, hn, h, h' => get_snoc_of_lt ρ v (by simpa using hn) h h'

theorem Env.get_snoc_of_eq {A : GlueTy α} : ∀ {Γ : List (GlueTy α)} (ρ : Env D Γ)
    (v : A.denote D) {n : ℕ} (_ : n = Γ.length) (h : (Γ ++ [A])[n]? = some A),
    (ρ.snoc v).get n h = v
  | _, .nil, _, 0, _, _ => rfl
  | _, .cons _ ρ, v, n + 1, hn, h => get_snoc_of_eq ρ v (by simpa using hn) h

/-- The meaning a proof assembles, applying for each elimination and abstracting for each
    introduction. -/
def Term.eval {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → Env D Γ → T.denote D
  | .var n h, ρ => ρ.get n h
  | .app f a, ρ => f.eval ρ (a.eval ρ)
  | .lam _ b, ρ => fun v ↦ b.eval (ρ.snoc v)

/-! ### Structural rules

Weakening, contraction and commutativity act on a proof by renaming the positions of its
premises. Commutativity preserves linearity and meaning; weakening and contraction destroy
linearity, so every premise is used exactly once. Asudeh takes this resource sensitivity to do
the work of Klein and Sag's bounded closure and of Kaplan and Bresnan's Completeness and
Coherence. -/

/-- Under a binder, a renaming `f` of `m` premises into `m'` extends to the hypotheses past the
    premises, which shift to follow the new ones. -/
def liftPos (m m' : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ := if n < m then f n else n - m + m'

theorem liftPos_liftPos (m m' : ℕ) (f : ℕ → ℕ) :
    liftPos (m + 1) (m' + 1) (liftPos m m' f) = liftPos m m' f := by
  funext n; simp only [liftPos]; split_ifs <;> omega

variable {Γ Γ' : List (GlueTy α)} {f : ℕ → ℕ}

private theorem lt_length_of_rename (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) {n : ℕ}
    (hn : n < Γ.length) : f n < Γ'.length :=
  (List.getElem?_eq_some_iff.1 (hf n _ (List.getElem?_eq_getElem hn))).1

theorem liftPos_getElem? (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) (A : GlueTy α) :
    ∀ n B, (Γ ++ [A])[n]? = some B →
      (Γ' ++ [A])[liftPos Γ.length Γ'.length f n]? = some B := by
  intro n B h
  unfold liftPos
  split_ifs with hn
  · rw [List.getElem?_append_left hn] at h
    rw [List.getElem?_append_left (lt_length_of_rename hf hn)]
    exact hf n B h
  · rw [List.getElem?_append_right (by omega)] at h
    rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel]

/-- Rename the premises of a proof along a map of positions that preserves their formulas. -/
def Term.rename : {Γ Γ' : List (GlueTy α)} → (f : ℕ → ℕ) →
    (∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) → {T : GlueTy α} → Term Γ T → Term Γ' T
  | _, _, f, hf, _, .var n h => .var (f n) (hf n _ h)
  | _, _, f, hf, _, .app s a => .app (s.rename f hf) (a.rename f hf)
  | Γ, Γ', f, hf, _, .lam A b =>
    .lam A (b.rename (liftPos Γ.length Γ'.length f) (liftPos_getElem? hf A))

theorem Term.uses_rename (f : ℕ → ℕ) (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B)
    {T : GlueTy α} (t : Term Γ T) :
    (t.rename f hf).uses = t.uses.map (liftPos Γ.length Γ'.length f) := by
  induction t generalizing Γ' f with
  | var n h => simp [rename, uses, liftPos, (List.getElem?_eq_some_iff.1 h).1]
  | app s a ihs iha => simp [rename, uses, ihs, iha]
  | lam A b ih =>
    simp only [rename, uses, ih, List.length_append, List.length_singleton, liftPos_liftPos]

theorem Term.HypLinear.rename (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B) {T : GlueTy α}
    {t : Term Γ T} (ht : t.HypLinear) : (t.rename f hf).HypLinear := by
  induction t generalizing Γ' f with
  | var => trivial
  | app s a ihs iha => exact ⟨ihs hf ht.1, iha hf ht.2⟩
  | @lam Γ A B b ih =>
    refine ⟨?_, ih _ ht.2⟩
    simp only [uses_rename, List.length_append, List.length_singleton, liftPos_liftPos]
    rw [List.count, List.countP_map, ← ht.1, List.count]
    refine List.countP_congr fun x _ ↦ ?_
    simp only [Function.comp_apply, beq_iff_eq, liftPos]
    split_ifs with hx
    · have := lt_length_of_rename hf hx; omega
    · omega

/-- Reordering the premises of a linear proof leaves it linear, so commutativity holds. -/
theorem Term.Linear.rename_perm {T : GlueTy α} {t : Term Γ T} (ht : t.Linear)
    (σ : Equiv.Perm ℕ) (hσ : ∀ n, Γ.length ≤ n → σ n = n) (hlen : Γ'.length = Γ.length)
    (hf : ∀ n B, Γ[n]? = some B → Γ'[σ n]? = some B) : (t.rename σ hf).Linear := by
  have hlift : liftPos Γ.length Γ'.length σ = σ := by
    funext n; simp only [liftPos, hlen]; split_ifs with hn
    · rfl
    · rw [hσ n (by omega)]; omega
  refine ⟨fun i hi ↦ ?_, ht.2.rename hf⟩
  have hsymm : σ.symm i < Γ.length := by
    by_contra h
    have := hσ (σ.symm i) (by omega)
    rw [Equiv.apply_symm_apply] at this
    omega
  rw [uses_rename, hlift, ← Equiv.apply_symm_apply σ i, List.count_map_of_injective _ _
    σ.injective]
  exact ht.1 _ hsymm

theorem Term.eval_rename (f : ℕ → ℕ) (hf : ∀ n B, Γ[n]? = some B → Γ'[f n]? = some B)
    {T : GlueTy α} (t : Term Γ T) (ρ : Env D Γ) (ρ' : Env D Γ')
    (hρ : ∀ n B (h : Γ[n]? = some B), ρ'.get (f n) (hf n B h) = ρ.get n h) :
    (t.rename f hf).eval ρ' = t.eval ρ := by
  induction t generalizing Γ' f with
  | var n h => exact hρ n _ h
  | app s a ihs iha => simp only [rename, eval, ihs f hf ρ ρ' hρ, iha f hf ρ ρ' hρ]
  | @lam Γ A B b ih =>
    funext v
    refine ih (liftPos Γ.length Γ'.length f) (liftPos_getElem? hf A) (ρ.snoc v) (ρ'.snoc v)
      fun n C h ↦ ?_
    by_cases hn : n < Γ.length
    · have h₁ : Γ[n]? = some C := by rwa [List.getElem?_append_left hn] at h
      have h₂ : (Γ' ++ [A])[f n]? = some C := by
        rw [List.getElem?_append_left (lt_length_of_rename hf hn)]; exact hf n C h₁
      rw [Env.get_congr _ (by simp only [liftPos, hn, ↓reduceIte]) _ h₂,
        Env.get_snoc_of_lt _ _ (lt_length_of_rename hf hn) h₂ (hf n C h₁),
        Env.get_snoc_of_lt _ _ hn h h₁, hρ]
    · have h₁ := h
      rw [List.getElem?_append_right (by omega)] at h₁
      have hlt := (List.getElem?_eq_some_iff.1 h₁).1
      obtain rfl : C = A := by simpa using List.mem_of_getElem? h₁
      simp only [List.length_singleton] at hlt
      rw [Env.get_snoc_of_eq _ _ (by simp only [liftPos, hn, ↓reduceIte]; omega),
        Env.get_snoc_of_eq _ _ (by omega)]

theorem getElem?_append_left_of_eq_some {A : GlueTy α} {n : ℕ} {B : GlueTy α}
    (h : Γ[n]? = some B) : (Γ ++ [A])[n]? = some B := by
  rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]

/-- Weakening adds a premise that the proof does not use. -/
def Term.weaken {T : GlueTy α} (A : GlueTy α) (t : Term Γ T) : Term (Γ ++ [A]) T :=
  t.rename id fun _ _ ↦ getElem?_append_left_of_eq_some

/-- A weakened proof is never linear, since its added premise is left over. -/
theorem Term.not_linear_weaken {T : GlueTy α} (A : GlueTy α) (t : Term Γ T) :
    ¬ (t.weaken A).Linear := by
  intro h
  have h₁ := h.1 Γ.length (by simp)
  rw [weaken, uses_rename, List.count_eq_zero.2] at h₁
  · exact absurd h₁ (by decide)
  · simp only [List.length_append, List.length_singleton, List.mem_map, not_exists, not_and,
      liftPos, id]
    intro x _; split_ifs <;> omega

theorem contract_getElem? {A : GlueTy α} :
    ∀ n B, (Γ ++ [A, A])[n]? = some B → (Γ ++ [A])[min n Γ.length]? = some B := by
  intro n B h
  rcases lt_or_ge n Γ.length with hn | hn
  · rw [min_eq_left hn.le, List.getElem?_append_left hn]
    rwa [List.getElem?_append_left hn] at h
  · rw [List.getElem?_append_right hn] at h
    obtain rfl : B = A := by simpa using List.mem_of_getElem? h
    simp [min_eq_right hn]

/-- Contraction lets one premise stand for two occurrences of its formula. -/
def Term.contract {A T : GlueTy α} (t : Term (Γ ++ [A, A]) T) : Term (Γ ++ [A]) T :=
  t.rename (fun n ↦ min n Γ.length) contract_getElem?

private theorem count_map_contract (m : ℕ) : ∀ l : List ℕ,
    (l.map (liftPos (m + 2) (m + 1) (fun n ↦ min n m))).count m = l.count m + l.count (m + 1)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.count_cons, count_map_contract m l, liftPos, beq_iff_eq]
    split_ifs <;> omega

/-- Contracting a linear proof never yields a linear one, since the merged premise is used
    twice. -/
theorem Term.Linear.not_linear_contract {A T : GlueTy α} {t : Term (Γ ++ [A, A]) T}
    (ht : t.Linear) : ¬ t.contract.Linear := by
  intro h
  have h₁ := h.1 Γ.length (by simp)
  have h₂ := ht.1 Γ.length (by simp)
  have h₃ := ht.1 (Γ.length + 1) (by simp)
  simp only [contract, uses_rename, List.length_append, List.length_cons,
    List.length_nil] at h₁
  rw [count_map_contract, h₂, h₃] at h₁
  omega

/-! ### Count invariance

The count of an atom in a formula is its positive occurrences less its negative ones. A linear
proof preserves counts, so a premise multiset whose counts differ from its conclusion's has no
linear proof at all. -/

/-- A formula is derivable from a multiset of premises if some ordering of them has a linear
    proof of it. -/
def Derivable (M : Multiset (GlueTy α)) (C : GlueTy α) : Prop :=
  ∃ Γ : List (GlueTy α), (Γ : Multiset (GlueTy α)) = M ∧ ∃ t : Term Γ C, t.Linear

section Count

variable [DecidableEq α]

/-- The count of an atom in a formula, its positive occurrences less its negative ones. -/
def GlueTy.count (x : α) : GlueTy α → ℤ
  | .atom a => if a = x then 1 else 0
  | .lolli A B => B.count x - A.count x

/-- The count of an atom in the formula at a position of a list, zero past its end. -/
def countAt (x : α) (Γ : List (GlueTy α)) (i : ℕ) : ℤ := ((Γ[i]?).map (GlueTy.count x)).getD 0

private theorem countAt_append (x : α) (Γ : List (GlueTy α)) (A : GlueTy α) (u : ℕ) :
    countAt x (Γ ++ [A]) u = countAt x Γ u + if u = Γ.length then A.count x else 0 := by
  unfold countAt
  rcases lt_trichotomy u Γ.length with h | rfl | h
  · simp [List.getElem?_append_left h, h.ne]
  · simp
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h.le]
    simp [h.ne']

private theorem sum_countAt_append (x : α) (Γ : List (GlueTy α)) (A : GlueTy α) :
    ∀ l : List ℕ, (l.map (countAt x (Γ ++ [A]))).sum =
      (l.map (countAt x Γ)).sum + l.count Γ.length * A.count x
  | [] => by simp
  | u :: l => by
    simp only [List.map_cons, List.sum_cons, List.count_cons, sum_countAt_append x Γ A l,
      countAt_append, beq_iff_eq]
    split_ifs <;> push_cast <;> ring

theorem Term.count_eq_sum (x : α) {T : GlueTy α} (t : Term Γ T) (ht : t.HypLinear) :
    T.count x = (t.uses.map (countAt x Γ)).sum := by
  induction t with
  | var n h => simp [uses, countAt, h]
  | app f a ihf iha =>
    simp only [uses, List.map_append, List.sum_append, ← ihf ht.1, ← iha ht.2, GlueTy.count]
    ring
  | @lam Γ A B b ih =>
    have h := ih ht.2
    rw [sum_countAt_append, ht.1] at h
    simp only [uses, GlueTy.count, h]
    push_cast; ring

/-- The conclusion of a linear proof has the total count of its premises, which is count
    invariance. -/
theorem Term.Linear.count_eq (x : α) {T : GlueTy α} {t : Term Γ T} (ht : t.Linear) :
    T.count x = (Γ.map (GlueTy.count x)).sum := by
  rw [t.count_eq_sum x ht.2]
  have hzero : ∀ l : List ℕ, (l.map (countAt x Γ)).sum =
      ((l.filter (· < Γ.length)).map (countAt x Γ)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons u l ih =>
      by_cases hu : u < Γ.length
      · simp [hu, ih]
      · simp [hu, ih, countAt]
  have hperm : (t.uses.filter (· < Γ.length)).Perm (List.range Γ.length) := by
    rw [List.perm_iff_count]
    intro a
    by_cases ha : a < Γ.length
    · rw [List.count_filter (by simpa using ha), ht.1 a ha, List.count_eq_one_of_mem
        List.nodup_range (List.mem_range.2 ha)]
    · rw [List.count_eq_zero.2 (by simp [ha]), List.count_eq_zero.2 (by simp [ha])]
  rw [hzero, (hperm.map _).sum_eq]
  congr 1
  refine List.ext_getElem (by simp) fun i _ h ↦ ?_
  simp [countAt, List.getElem?_eq_getElem (by simpa using h : i < Γ.length)]

theorem Derivable.count_eq {M : Multiset (GlueTy α)} {C : GlueTy α} (h : Derivable M C)
    (x : α) : C.count x = (M.map (GlueTy.count x)).sum := by
  obtain ⟨Γ, rfl, t, ht⟩ := h
  rw [ht.count_eq x, Multiset.map_coe, Multiset.sum_coe]

end Count

/-! ### Proof nets

A proof net forgets the order in which a proof applies its rules. The sequent `Γ ⊢ C` is read
with its premises negative and its conclusion positive, so that a negative implication is a
tensor and a positive one a par, and a net links every negative atom occurrence to a positive
occurrence of the same atom. By Danos and Regnier's criterion, a linking is a proof when every
switching, which keeps one of the two edges at each par, leaves a tree. -/

namespace GlueTy

/-- The subformula occurrences of a formula, as paths from its root. -/
inductive Node : GlueTy α → Type _
  | root {A : GlueTy α} : Node A
  | left {A B : GlueTy α} : Node A → Node (A ⊸ B)
  | right {A B : GlueTy α} : Node B → Node (A ⊸ B)

/-- The path to a node, `false` for each step into an antecedent and `true` for each step into a
    consequent. -/
def Node.path : {A : GlueTy α} → A.Node → List Bool
  | _, .root => []
  | _, .left n => false :: n.path
  | _, .right n => true :: n.path

theorem Node.path_injective : ∀ {A : GlueTy α}, Function.Injective (Node.path (A := A))
  | _, .root, .root, _ => rfl
  | _, .left _, .left _, h => by rw [path_injective (List.cons_injective h)]
  | _, .right _, .right _, h => by rw [path_injective (List.cons_injective h)]
  | _, .root, .left _, h | _, .root, .right _, h | _, .left _, .root, h
  | _, .right _, .root, h | _, .left _, .right _, h | _, .right _, .left _, h => by
    simp [path] at h

instance (A : GlueTy α) : DecidableEq A.Node :=
  fun _ _ ↦ decidable_of_iff _ Node.path_injective.eq_iff

/-- The subformula occurrences of a formula, root first. -/
def Node.all : (A : GlueTy α) → List A.Node
  | .atom _ => [.root]
  | .lolli A B => .root :: ((Node.all A).map .left ++ (Node.all B).map .right)

theorem Node.mem_all : ∀ {A : GlueTy α} (n : A.Node), n ∈ Node.all A
  | .atom _, .root => List.mem_singleton_self _
  | .lolli _ _, .root => List.mem_cons_self
  | .lolli _ _, .left n =>
    List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem (mem_all n)))
  | .lolli _ _, .right n =>
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem (mem_all n)))

theorem Node.nodup_all : ∀ A : GlueTy α, (Node.all A).Nodup
  | .atom _ => List.nodup_singleton _
  | .lolli A B => by
    refine List.nodup_cons.2 ⟨by simp, List.nodup_append.2 ⟨
      (nodup_all A).map fun _ _ h ↦ by cases h; rfl,
      (nodup_all B).map fun _ _ h ↦ by cases h; rfl, ?_⟩⟩
    simp

instance (A : GlueTy α) : Fintype A.Node := ⟨⟨Node.all A, Node.nodup_all A⟩, Node.mem_all⟩

/-- The subformula at a node. -/
def Node.sub : {A : GlueTy α} → A.Node → GlueTy α
  | A, .root => A
  | _, .left n => n.sub
  | _, .right n => n.sub

/-- Whether a node lies under an odd number of antecedents. -/
def Node.flip : {A : GlueTy α} → A.Node → Bool
  | _, .root => false
  | _, .left n => !n.flip
  | _, .right n => n.flip

/-- Whether `c` is the antecedent (`false`) or the consequent (`true`) child of `p`. -/
def Node.childDir : {A : GlueTy α} → A.Node → A.Node → Option Bool
  | _, .root, .left .root => some false
  | _, .root, .right .root => some true
  | _, .left p, .left c => p.childDir c
  | _, .right p, .right c => p.childDir c
  | _, _, _ => none

/-- The atom a formula is, if it is one. -/
def label? : GlueTy α → Option α
  | .atom a => some a
  | .lolli _ _ => none

end GlueTy

section Reach

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertices reachable from `v` in at most `k` steps. -/
def reachWithin (v : V) : ℕ → Finset V
  | 0 => {v}
  | k + 1 => (reachWithin v k).biUnion fun u ↦ insert u (Finset.univ.filter (G.Adj u))

variable {G}

theorem mem_reachWithin_succ {v w : V} {k : ℕ} :
    w ∈ reachWithin G v (k + 1) ↔ ∃ u ∈ reachWithin G v k, w = u ∨ G.Adj u w := by
  simp [reachWithin]

theorem reachWithin_mono (v : V) {k m : ℕ} (h : k ≤ m) :
    reachWithin G v k ⊆ reachWithin G v m := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans fun w hw ↦ mem_reachWithin_succ.2 ⟨w, hw, .inl rfl⟩

theorem reachable_of_mem_reachWithin {v w : V} :
    ∀ {k}, w ∈ reachWithin G v k → G.Reachable v w
  | 0, h => by rw [Finset.mem_singleton.1 h]
  | _ + 1, h => by
    obtain ⟨u, hu, rfl | huw⟩ := mem_reachWithin_succ.1 h
    · exact reachable_of_mem_reachWithin hu
    · exact (reachable_of_mem_reachWithin hu).trans huw.reachable

theorem reachWithin_subset_of_adj {v u : V} (h : G.Adj v u) :
    ∀ k, reachWithin G u k ⊆ reachWithin G v (k + 1)
  | 0 => fun w hw ↦ mem_reachWithin_succ.2 ⟨v, by simp [reachWithin], .inr (by
      rw [Finset.mem_singleton.1 hw]; exact h)⟩
  | k + 1 => fun w hw ↦ by
    obtain ⟨x, hx, hxw⟩ := mem_reachWithin_succ.1 hw
    exact mem_reachWithin_succ.2 ⟨x, reachWithin_subset_of_adj h k hx, hxw⟩

theorem mem_reachWithin_length {v w : V} : ∀ p : G.Walk v w, w ∈ reachWithin G v p.length
  | .nil => Finset.mem_singleton_self _
  | .cons h p => reachWithin_subset_of_adj h _ (mem_reachWithin_length p)

theorem connected_iff_reachWithin (v : V) :
    G.Connected ↔ reachWithin G v (Fintype.card V) = Finset.univ := by
  refine ⟨fun hG ↦ Finset.eq_univ_of_forall fun w ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨p, hp⟩ := (hG v w).exists_isPath
    exact reachWithin_mono v hp.length_lt.le (mem_reachWithin_length p)
  · have hr (w : V) : G.Reachable v w := reachable_of_mem_reachWithin (h ▸ Finset.mem_univ w)
    have : Nonempty V := ⟨v⟩
    exact ⟨fun u w ↦ (hr u).symm.trans (hr w)⟩

theorem isTree_iff_reachWithin (v : V) :
    G.IsTree ↔ reachWithin G v (Fintype.card V) = Finset.univ ∧
      ∑ w, G.degree w + 2 = 2 * Fintype.card V := by
  simp only [SimpleGraph.isTree_iff_connected_and_card, connected_iff_reachWithin v,
    SimpleGraph.sum_degrees_eq_twice_card_edges, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card]
  exact and_congr Iff.rfl (by omega)

end Reach

/-- A one-sided sequent lists formulas with their polarities. -/
abbrev Sequent (α : Type*) := List (Bool × GlueTy α)

/-- The sequent of premises `Γ` and conclusion `C`, the premises negative. -/
def Sequent.of (Γ : List (GlueTy α)) (C : GlueTy α) : Sequent α :=
  Γ.map (false, ·) ++ [(true, C)]

namespace Sequent

variable (S : Sequent α)

/-- The subformula occurrences of a sequent. -/
abbrev Vert := Σ i : Fin S.length, (S[i]).2.Node

instance (priority := high) : DecidableEq S.Vert := fun u v ↦
  decidable_of_iff ((u.1 : ℕ) = v.1 ∧ u.2.path = v.2.path) <| by
    obtain ⟨⟨i, hi⟩, a⟩ := u
    obtain ⟨⟨j, hj⟩, b⟩ := v
    constructor
    · rintro ⟨rfl, h⟩
      exact Sigma.ext rfl (heq_of_eq (GlueTy.Node.path_injective h))
    · rintro h
      cases h
      exact ⟨rfl, rfl⟩

/-- The polarity of an occurrence. -/
def pol (v : S.Vert) : Bool := (S[v.1]).1 != v.2.flip

/-- The atom an occurrence is, if it is one. -/
def label? (v : S.Vert) : Option α := v.2.sub.label?

/-- The negative atom occurrences. -/
abbrev Neg := {v : S.Vert // (S.label? v).isSome ∧ S.pol v = false}

/-- The positive atom occurrences. -/
abbrev Pos := {v : S.Vert // (S.label? v).isSome ∧ S.pol v = true}

/-- A par is a positive implication; a switching keeps one of its two edges. -/
def IsPar (v : S.Vert) : Prop := (S.label? v).isNone ∧ S.pol v = true

instance : DecidablePred S.IsPar := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A switching chooses an edge at each par. -/
abbrev Switching := {v : S.Vert // S.IsPar v} → Bool

/-- The direction of the formula-tree edge from `p` down to `c`, if there is one. -/
def edgeDir : S.Vert → S.Vert → Option Bool
  | ⟨i, p⟩, ⟨j, c⟩ => if h : i = j then (h ▸ p).childDir c else none

/-- The switching keeps the formula-tree edge from `p` down to `c`. -/
def kept (σ : S.Switching) (p c : S.Vert) : Bool :=
  match S.edgeDir p c with
  | some b => if h : S.IsPar p then σ ⟨p, h⟩ == b else true
  | none => false

variable [DecidableEq α]

/-- A linking pairs each negative atom occurrence with a positive occurrence of the same atom. -/
abbrev Linking := {e : S.Neg ≃ S.Pos // ∀ v, S.label? (e v).1 = S.label? v.1}

variable {S}

/-- The axiom link from a negative occurrence `u` to `v`. -/
def Linking.ax (L : S.Linking) (u v : S.Vert) : Bool :=
  if h : (S.label? u).isSome ∧ S.pol u = false then (L.1 ⟨u, h⟩).1 == v else false

/-- The switching graph keeps the chosen formula-tree edges and every axiom link. -/
def Linking.graph (L : S.Linking) (σ : S.Switching) : SimpleGraph S.Vert :=
  SimpleGraph.fromRel fun u v ↦ S.kept σ u v ∨ L.ax u v

instance (L : S.Linking) (σ : S.Switching) : DecidableRel (L.graph σ).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A linking is correct if every switching graph is a tree. -/
def Linking.Correct (L : S.Linking) : Prop := ∀ σ, (L.graph σ).IsTree

/-- The root of the last formula. -/
def lastRoot (h : 0 < S.length) : S.Vert := ⟨⟨S.length - 1, by omega⟩, .root⟩

instance (L : S.Linking) (σ : S.Switching) : Decidable (L.graph σ).IsTree :=
  if h : 0 < S.length then decidable_of_iff _ (isTree_iff_reachWithin (lastRoot h)).symm
  else isFalse fun hT ↦ by
    obtain ⟨v⟩ := hT.connected.nonempty
    exact absurd v.1.2 (by omega)

instance (L : S.Linking) : Decidable L.Correct := inferInstanceAs (Decidable (∀ _, _))

end Sequent

/-- A sequent is derivable exactly when it has a correct proof net. -/
theorem derivable_iff_exists_correct [DecidableEq α] (Γ : List (GlueTy α)) (C : GlueTy α) :
    Derivable (Γ : Multiset (GlueTy α)) C ↔ ∃ L : (Sequent.of Γ C).Linking, L.Correct := by
  -- TODO: Desequentialization: by induction on a linear term, with a variable linking its
  -- formula to itself, an application joining two nets through a tensor and an abstraction
  -- adding a par. Sequentialization: split a correct net at a splitting tensor or a terminal par.
  sorry

namespace GlueTy

private theorem card_node_subtype (A : GlueTy α) (P : A.Node → Prop) [DecidablePred P] :
    Fintype.card {n : A.Node // P n} = (Node.all A).countP fun n ↦ P n := by
  rw [Fintype.card_subtype, List.countP_eq_length_filter]
  rfl

variable [DecidableEq α]

/-- The occurrences of `x` under an even (`false`) or odd (`true`) number of antecedents. -/
def leafCount (A : GlueTy α) (x : α) (b : Bool) : ℕ :=
  (Node.all A).countP fun n ↦ n.sub.label? = some x ∧ n.flip = b

theorem count_eq_leafCount : ∀ (A : GlueTy α) (x : α),
    A.count x = (A.leafCount x false : ℤ) - A.leafCount x true
  | .atom a, x => by
    by_cases h : a = x <;> simp [leafCount, Node.all, count, Node.sub, Node.flip, label?, h]
  | .lolli A B, x => by
    have hl (b : Bool) : ((Node.all A).map (Node.left (B := B))).countP
        (fun n ↦ n.sub.label? = some x ∧ n.flip = b) = A.leafCount x (!b) := by
      rw [List.countP_map, leafCount]
      refine List.countP_congr fun n _ ↦ ?_
      cases b <;> simp only [Function.comp_apply, Node.sub, Node.flip, decide_eq_true_iff,
        Bool.not_false, Bool.not_true, Bool.not_eq_true', Bool.not_eq_false']
    have hr (b : Bool) : ((Node.all B).map (Node.right (A := A))).countP
        (fun n ↦ n.sub.label? = some x ∧ n.flip = b) = B.leafCount x b := by
      rw [List.countP_map, leafCount]
      rfl
    have h0 (b : Bool) : decide ((Node.root : (A ⊸ B).Node).sub.label? = some x ∧
        (Node.root : (A ⊸ B).Node).flip = b) = false := by
      simp [Node.sub, label?]
    have e (b : Bool) : (A ⊸ B).leafCount x b = ((Node.all A).map (Node.left (B := B)) ++
        (Node.all B).map (Node.right (A := A))).countP
          (fun n : (A ⊸ B).Node ↦ n.sub.label? = some x ∧ n.flip = b) +
          if decide ((Node.root : (A ⊸ B).Node).sub.label? = some x ∧
            (Node.root : (A ⊸ B).Node).flip = b) then 1 else 0 :=
      List.countP_cons
    rw [count, count_eq_leafCount A x, count_eq_leafCount B x, e, e, List.countP_append,
      List.countP_append, hl, hl, hr, hr, h0, h0, Bool.not_false, Bool.not_true]
    push_cast
    ring

end GlueTy

private theorem card_subtype_sigma {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)]
    (P : (Σ i, β i) → Prop) [DecidablePred P] :
    Fintype.card {v // P v} = ∑ i, Fintype.card {n : β i // P ⟨i, n⟩} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr ⟨fun v ↦ ⟨v.1.1, v.1.2, v.2⟩, fun w ↦ ⟨⟨w.1, w.2.1⟩, w.2.2⟩,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

namespace Sequent

variable [DecidableEq α]

/-- The number of occurrences of `x` of polarity `p` in a sequent. -/
def occCount (S : Sequent α) (x : α) (p : Bool) : ℕ :=
  Fintype.card {v : S.Vert // S.label? v = some x ∧ S.pol v = p}

theorem occCount_eq (S : Sequent α) (x : α) (p : Bool) :
    S.occCount x p = (S.map fun F ↦ F.2.leafCount x (F.1 != p)).sum := by
  rw [occCount, card_subtype_sigma, ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [GlueTy.card_node_subtype, GlueTy.leafCount]
  have key : ∀ a f q : Bool, ((a != f) = q) = (f = (a != q)) := by decide
  simp only [label?, pol, key]
  rfl

private theorem sum_map_count (x : α) : ∀ Γ : List (GlueTy α),
    (Γ.map (GlueTy.count x)).sum =
      (((Γ.map fun A ↦ A.leafCount x false).sum : ℕ) : ℤ) -
        (((Γ.map fun A ↦ A.leafCount x true).sum : ℕ) : ℤ)
  | [] => by simp
  | A :: Γ => by
    simp only [List.map_cons, List.sum_cons, sum_map_count x Γ, GlueTy.count_eq_leafCount A x]
    push_cast; ring

variable {S : Sequent α}

/-- A linking pairs the negative and the positive occurrences of each atom one to one. -/
def Linking.equivLabel (L : S.Linking) (x : α) :
    {v : S.Vert // S.label? v = some x ∧ S.pol v = false} ≃
      {v : S.Vert // S.label? v = some x ∧ S.pol v = true} where
  toFun v := ⟨(L.1 ⟨v.1, by simp [v.2.1], v.2.2⟩).1, by rw [L.2]; exact ⟨v.2.1, (L.1 _).2.2⟩⟩
  invFun v := ⟨(L.1.symm ⟨v.1, by simp [v.2.1], v.2.2⟩).1, by
    have := L.2 (L.1.symm ⟨v.1, by simp [v.2.1], v.2.2⟩)
    rw [Equiv.apply_symm_apply] at this
    exact ⟨this ▸ v.2.1, (L.1.symm _).2.2⟩⟩
  left_inv v := by simp
  right_inv v := by simp

theorem Linking.count_eq {Γ : List (GlueTy α)} {C : GlueTy α} (L : (Sequent.of Γ C).Linking)
    (x : α) : C.count x = (Γ.map (GlueTy.count x)).sum := by
  have h := Fintype.card_congr (L.equivLabel x)
  rw [← occCount, ← occCount, occCount_eq, occCount_eq] at h
  simp only [Sequent.of, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    List.map_singleton, List.sum_singleton, bne_self_eq_false, Bool.bne_false,
    Bool.false_bne] at h
  rw [GlueTy.count_eq_leafCount, sum_map_count]
  omega

end Sequent

/-! ### The substructural hierarchy

A logic is characterized by the structural rules it admits, and admitting more rules makes it
stronger. The Lambek calculus admits none, linear logic commutativity only; relevance logic adds
contraction, affine logic weakening, and intuitionistic logic both. -/

/-- The structural rules whose presence or absence characterizes a logic. -/
inductive StructuralRule
  | weakening
  | contraction
  | commutativity
  deriving DecidableEq

/-- A logic, by the structural rules it admits. -/
abbrev Logic := Finset StructuralRule

/-- The Lambek calculus admits no structural rules. -/
def Logic.lambek : Logic := ∅

/-- Linear logic admits commutativity only. -/
def Logic.linear : Logic := {.commutativity}

/-- A resource logic admits neither weakening nor contraction. -/
def Logic.Resource (l : Logic) : Prop := .weakening ∉ l ∧ .contraction ∉ l

theorem resource_iff (l : Logic) : l.Resource ↔ l = .lambek ∨ l = .linear := by
  rw [Logic.lambek, Logic.linear, ← Finset.subset_singleton_iff, Finset.subset_singleton_iff']
  constructor
  · rintro ⟨hw, hc⟩ r hr
    cases r <;> simp_all
  · intro h
    exact ⟨fun hw ↦ StructuralRule.noConfusion (h _ hw),
      fun hc ↦ StructuralRule.noConfusion (h _ hc)⟩

theorem commutative_resource_iff (l : Logic) :
    l.Resource ∧ .commutativity ∈ l ↔ l = .linear := by
  rw [resource_iff]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · simp [Logic.lambek] at h
    · rfl
  · rintro rfl
    exact ⟨.inr rfl, by simp [Logic.linear]⟩

/-! ### The paper's proofs -/

/-- The instantiated atoms of the paper's examples. -/
inductive Label
  | a | b | c | l | e | s | p | w | d
  deriving DecidableEq, Repr

open GlueTy (atom)

/-- Recurrying by hypothetical reasoning turns a head taking `a` then `b` into one taking `b`
    then `a`, discharging both hypotheses. -/
def recurry :
    Term [atom Label.a ⊸ atom Label.b ⊸ atom Label.c]
      (atom Label.b ⊸ atom Label.a ⊸ atom Label.c) :=
  .lam (atom Label.b) (.lam (atom Label.a) (.app (.app (.var 0 rfl) (.var 2 rfl)) (.var 1 rfl)))

theorem recurry_linear : recurry.Linear := by decide

theorem recurry_eval {D : Label → Type} (f : D .a → D .b → D .c) :
    recurry.eval (.cons f .nil) = fun u v ↦ f v u :=
  rfl

/-- The meaning constructors of *Alex likes Blake*, word by word. -/
def alexLikesBlake : List (List (GlueTy Label)) :=
  [[atom Label.a], [atom Label.b ⊸ atom Label.a ⊸ atom Label.l], [atom Label.b]]

/-- The single normal-form proof applies *likes* to *Blake* and then to *Alex*, taking the
    premises out of word order. -/
def likesProof : Term alexLikesBlake.flatten (atom Label.l) :=
  .app (.app (.var 1 rfl) (.var 2 rfl)) (.var 0 rfl)

theorem likesProof_linear : likesProof.Linear := by decide

theorem likesProof_eval {D : Label → Type} (alex : D .a) (like : D .b → D .a → D .l)
    (blake : D .b) : likesProof.eval (.cons alex (.cons like (.cons blake .nil))) =
      like blake alex :=
  rfl

/-- The meaning constructors of Finnish *Join vettä*, where *join* contributes the speaker and
    the drinking and *vettä* the water. -/
def finnish : List (List (GlueTy Label)) :=
  [[atom Label.p, atom Label.w ⊸ atom Label.p ⊸ atom Label.d], [atom Label.w]]

/-- The meaning constructors of English *I drank water*, one per word. -/
def english : List (List (GlueTy Label)) :=
  [[atom Label.p], [atom Label.w ⊸ atom Label.p ⊸ atom Label.d], [atom Label.w]]

/-- Two words and three words instantiate the same premises. -/
theorem finnish_english : finnish.flatten = english.flatten ∧ finnish.length ≠ english.length :=
  by decide

/-- The one normal-form proof of *I drank water* in either language. -/
def drinkProof : Term english.flatten (atom Label.d) :=
  .app (.app (.var 1 rfl) (.var 2 rfl)) (.var 0 rfl)

theorem drinkProof_linear : drinkProof.Linear := by decide

theorem drinkProof_eval {D : Label → Type} (speaker : D .p) (drink : D .w → D .p → D .d)
    (water : D .w) : drinkProof.eval (.cons speaker (.cons drink (.cons water .nil))) =
      drink water speaker :=
  rfl

/-- The meaning constructors of *Everybody loves somebody*, word by word, with both quantifiers'
    scope instantiated to the clause. -/
def everybodyLovesSomebody : List (List (GlueTy Label)) :=
  [[(atom Label.e ⊸ atom Label.l) ⊸ atom Label.l], [atom Label.s ⊸ atom Label.e ⊸ atom Label.l],
    [(atom Label.s ⊸ atom Label.l) ⊸ atom Label.l]]

/-- Surface scope hypothesizes the object and then the subject, discharges the object under
    *somebody* and then the subject under *everybody*. -/
def surface : Term everybodyLovesSomebody.flatten (atom Label.l) :=
  .app (.var 0 rfl) (.lam (atom Label.e)
    (.app (.var 2 rfl) (.lam (atom Label.s) (.app (.app (.var 1 rfl) (.var 4 rfl)) (.var 3 rfl)))))

/-- Inverse scope hypothesizes the object only, applies *everybody* to *loves* of it, and
    discharges the object under *somebody*. -/
def inverse : Term everybodyLovesSomebody.flatten (atom Label.l) :=
  .app (.var 2 rfl) (.lam (atom Label.s) (.app (.var 0 rfl) (.app (.var 1 rfl) (.var 3 rfl))))

theorem surface_linear : surface.Linear := by decide

theorem inverse_linear : inverse.Linear := by decide

/-- *Everybody loves somebody* has exactly two correct proof nets, the two normal-form proofs
    the paper finds for it. -/
theorem card_correct_loves :
    Fintype.card {L : (Sequent.of everybodyLovesSomebody.flatten (atom Label.l)).Linking //
      L.Correct} = 2 := by
  decide +kernel

/-- The occurrence of the clause the sentence proves. -/
def lovesGoal : (Sequent.of everybodyLovesSomebody.flatten (atom Label.l)).Pos :=
  ⟨⟨⟨3, by decide⟩, .root⟩, by decide⟩

private theorem not_correct_of_clause_from_loves :
    ∀ L : (Sequent.of everybodyLovesSomebody.flatten (atom Label.l)).Linking,
      ((L.1.symm lovesGoal).1.1 : ℕ) = 1 → ¬ L.Correct := by
  decide +kernel

theorem clause_from_quantifier
    {L : (Sequent.of everybodyLovesSomebody.flatten (atom Label.l)).Linking} (hL : L.Correct) :
    ((L.1.symm lovesGoal).1.1 : ℕ) ≠ 1 :=
  fun h ↦ not_correct_of_clause_from_loves L h hL

/-- Clause atoms denote propositions and argument atoms entities. -/
def Label.ty : Label → Montague.Ty
  | .l | .c | .d => .t
  | _ => .e

/-- The premises mean *every person*, *love* and *some person*, the two quantifiers being the
    generalized quantifiers of the determiners. -/
def scopeEnv {E : Type} (person : E → Prop) (love : E → E → Prop) :
    Env (fun x ↦ Montague.Ty.Domain E Unit x.ty) everybodyLovesSomebody.flatten :=
  .cons (every person) (.cons love (.cons (Det.some person) .nil))

/-- The surface proof means the surface-scope reading, every person loving some person. -/
theorem surface_eval {E : Type} (person : E → Prop) (love : E → E → Prop) :
    surface.eval (scopeEnv person love) =
      surfaceScope every Det.some person person fun x y ↦ love y x :=
  rfl

/-- The inverse proof means the inverse-scope reading, some person loved by every person. -/
theorem inverse_eval {E : Type} (person : E → Prop) (love : E → E → Prop) :
    inverse.eval (scopeEnv person love) =
      inverseScope every Det.some person person fun x y ↦ love y x :=
  rfl

open HeimKratzer1998.Toy (person sees) in
open PhraseStructure.Tree (interp) in
/-- One set of premises yields, by its two proofs, what Heim and Kratzer's engine computes from
    their two Quantifier Raising trees. -/
theorem interp_qr_eq_eval :
    interp HeimKratzer1998.lex HeimKratzer1998.g₀ HeimKratzer1998.tree_surface =
        some ⟨.t, surface.eval (scopeEnv person sees)⟩ ∧
      interp HeimKratzer1998.lex HeimKratzer1998.g₀ HeimKratzer1998.tree_inverse =
        some ⟨.t, inverse.eval (scopeEnv person sees)⟩ :=
  ⟨HeimKratzer1998.interp_computes_surface, HeimKratzer1998.interp_computes_inverse⟩

open HeimKratzer1998.Toy (person sees) in
theorem readings_differ :
    surface.eval (scopeEnv person sees) ∧ ¬ inverse.eval (scopeEnv person sees) :=
  ⟨HeimKratzer1998.surface_scope_true, HeimKratzer1998.inverse_scope_false⟩

/-! ### Completeness and Coherence

Asudeh takes resource sensitivity to do the work of Completeness and Coherence. The Dutch
cross-serial clauses of Bresnan, Kaplan, Peters and Zaenen test the claim: their f-structure
spine is complete and coherent exactly when its objects match its non-final verbs, and exactly
then do the meaning constructors it instantiates have a linear proof of the clause. -/

open BresnanEtAl1982 (Spine subjOfVerb npOfObj subjOfVerb_eq)

/-- The atoms of a Dutch clause's semantic structure, for its noun phrases and for the clause
    each verb heads. -/
inductive DutchAtom
  | np (j : ℕ)
  | clause (i : ℕ)
  deriving DecidableEq

/-- The meaning constructor of the verb at depth `i`. A non-final verb takes its complement as a
    property of the complement's subject, which functional control identifies with the verb's
    object, then the object and its own subject; the final verb takes its subject alone. -/
def verbPremise (s : Spine) (i : ℕ) : GlueTy DutchAtom :=
  if i + 1 < s.verbs then
    (atom (.np (subjOfVerb (i + 1))) ⊸ atom (.clause (i + 1))) ⊸ atom (.np (npOfObj i)) ⊸
      atom (.np (subjOfVerb i)) ⊸ atom (.clause i)
  else atom (.np (subjOfVerb i)) ⊸ atom (.clause i)

/-- The premises at the `d` depths from `i`, the object and the verb at each. -/
def premisesFrom (s : Spine) : ℕ → ℕ → List (GlueTy DutchAtom)
  | 0, _ => []
  | d + 1, i => (if i < s.objects then [atom (.np (npOfObj i))] else []) ++
      (if i < s.verbs then [verbPremise s i] else []) ++ premisesFrom s d (i + 1)

/-- The premises of a spine are the objects and verbs at every depth and the subject. -/
def premises (s : Spine) : Multiset (GlueTy DutchAtom) :=
  ↑(premisesFrom s (max s.objects s.verbs) 0 ++ [atom (DutchAtom.np 0)])

private theorem count_verbPremise (s : Spine) (i j : ℕ) :
    (verbPremise s i).count (.np j) = -(if i = j then 1 else 0) := by
  unfold verbPremise
  split_ifs <;> simp_all [GlueTy.count, subjOfVerb_eq, npOfObj]

private theorem sum_count_obj (s : Spine) (i j : ℕ) :
    ((if i < s.objects then [atom (DutchAtom.np (npOfObj i))] else []).map
      (GlueTy.count (.np j))).sum = if i < s.objects ∧ i + 1 = j then 1 else 0 := by
  by_cases h : i < s.objects <;> simp [h, GlueTy.count, npOfObj]

private theorem sum_count_verb (s : Spine) (i j : ℕ) :
    ((if i < s.verbs then [verbPremise s i] else []).map (GlueTy.count (.np j))).sum =
      -(if i < s.verbs ∧ i = j then 1 else 0) := by
  by_cases h : i < s.verbs <;> simp [h, count_verbPremise]

private theorem sum_count_premisesFrom (s : Spine) (j : ℕ) : ∀ d i,
    ((premisesFrom s d i).map (GlueTy.count (.np j))).sum =
      (if i < j ∧ j ≤ i + d ∧ j ≤ s.objects then 1 else 0) -
        (if i ≤ j ∧ j < i + d ∧ j < s.verbs then 1 else 0)
  | 0, i => by simp only [premisesFrom, List.map_nil, List.sum_nil]; split_ifs <;> omega
  | d + 1, i => by
    simp only [premisesFrom, List.map_append, List.sum_append]
    rw [sum_count_obj, sum_count_verb, sum_count_premisesFrom s j d]
    have hp : (if i < s.objects ∧ i + 1 = j then 1 else 0 : ℤ) +
        (if i + 1 < j ∧ j ≤ i + 1 + d ∧ j ≤ s.objects then 1 else 0) =
          if i < j ∧ j ≤ i + (d + 1) ∧ j ≤ s.objects then 1 else 0 := by
      split_ifs <;> omega
    have hn : (if i < s.verbs ∧ i = j then 1 else 0 : ℤ) +
        (if i + 1 ≤ j ∧ j < i + 1 + d ∧ j < s.verbs then 1 else 0) =
          if i ≤ j ∧ j < i + (d + 1) ∧ j < s.verbs then 1 else 0 := by
      split_ifs <;> omega
    linarith

private theorem sum_count_premises (s : Spine) (j : ℕ) :
    ((premises s).map (GlueTy.count (.np j))).sum =
      (if j ≤ s.objects then 1 else 0) - (if j < s.verbs then 1 else 0) := by
  simp only [premises, Multiset.map_coe, Multiset.sum_coe, List.map_append, List.sum_append,
    sum_count_premisesFrom, List.map_singleton, List.sum_singleton, GlueTy.count,
    DutchAtom.np.injEq]
  have := le_max_left s.objects s.verbs
  have := le_max_right s.objects s.verbs
  split_ifs <;> omega

theorem complete_coherent_of_derivable {s : Spine} (hv : 1 ≤ s.verbs)
    (h : Derivable (premises s) (atom (.clause 0))) : s.Complete ∧ s.Coherent := by
  rw [Spine.complete_and_coherent_iff s hv]
  have key (j : ℕ) := h.count_eq (.np j)
  simp only [sum_count_premises, GlueTy.count, reduceCtorEq, ↓reduceIte] at key
  have h₁ := key s.objects
  have h₂ := key (s.verbs - 1)
  split_ifs at h₁ h₂ <;> omega

private theorem verbPremise_of_lt {n i : ℕ} (h : i < n) :
    verbPremise ⟨n, n + 1⟩ i = ((atom (.np (subjOfVerb (i + 1))) ⊸ atom (.clause (i + 1))) ⊸
      atom (.np (npOfObj i)) ⊸ atom (.np (subjOfVerb i)) ⊸ atom (.clause i)) := by
  simp [verbPremise, h]

private theorem premisesFrom_of_lt {n d i : ℕ} (h : i < n) :
    premisesFrom ⟨n, n + 1⟩ (d + 1) i =
      atom (.np (npOfObj i)) :: verbPremise ⟨n, n + 1⟩ i :: premisesFrom ⟨n, n + 1⟩ d (i + 1) := by
  simp [premisesFrom, h, show i < n + 1 by omega]

private theorem premisesFrom_last (n : ℕ) :
    premisesFrom ⟨n, n + 1⟩ 1 n = [atom (DutchAtom.np (subjOfVerb n)) ⊸ atom (.clause n)] := by
  simp [premisesFrom, verbPremise]

open DutchAtom in
/-- The proof from the premises at the depths from `i` and the subject of the verb at `i`
    applies that verb to the property its complement proves, its object and its subject. -/
def build (n : ℕ) : (d i : ℕ) → i + d = n →
    Term (premisesFrom ⟨n, n + 1⟩ (d + 1) i ++ [atom (np (subjOfVerb i))]) (atom (clause i))
  | 0, i, h =>
    .app (.var 0 (T := atom (np (subjOfVerb i)) ⊸ atom (clause i))
        (by obtain rfl : i = n := (by omega); simp [premisesFrom_last]))
      (.var 1 (by obtain rfl : i = n := (by omega); simp [premisesFrom_last]))
  | d + 1, i, h =>
    .app (.app (.app
          (.var 1 (T := (atom (np (subjOfVerb (i + 1))) ⊸ atom (clause (i + 1))) ⊸
            atom (np (npOfObj i)) ⊸ atom (np (subjOfVerb i)) ⊸ atom (clause i))
          (by rw [premisesFrom_of_lt (by omega), verbPremise_of_lt (by omega)]; rfl))
          ((Term.lam (atom (np (subjOfVerb (i + 1)))) (build n d (i + 1) (by omega))).rename
            (· + 2)
            fun k B hk ↦ by
              rw [premisesFrom_of_lt (by omega)]
              simpa [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1] using hk))
        (.var 0 (T := atom (np (npOfObj i)))
          (by rw [premisesFrom_of_lt (by omega)]; rfl)))
      (.var ((premisesFrom ⟨n, n + 1⟩ (d + 1) (i + 1)).length + 2)
        (T := atom (np (subjOfVerb i))) (by rw [premisesFrom_of_lt (by omega)]; simp))

open DutchAtom in
theorem build_linear (n : ℕ) : ∀ d i (h : i + d = n), (build n d i h).Linear
  | 0, i, h => by
    obtain rfl : i = n := by omega
    refine ⟨fun k hk ↦ ?_, by simp [build, Term.HypLinear]⟩
    simp only [Nat.zero_add, premisesFrom_last, List.length_append, List.length_singleton] at hk
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals simp [build, Term.uses]
  | d + 1, i, h => by
    have ih := build_linear n d (i + 1) (by omega)
    set L := (premisesFrom ⟨n, n + 1⟩ (d + 1) (i + 1)).length with hL
    have hlen : (premisesFrom ⟨n, n + 1⟩ (d + 2) i ++ [atom (np (subjOfVerb i))]).length =
        L + 3 := by
      rw [premisesFrom_of_lt (by omega)]; simp [L]
    have hg : Function.Injective (liftPos L (L + 3) (· + 2)) := fun u v huv ↦ by
      simp only [liftPos] at huv; split_ifs at huv <;> omega
    have hlam :
        (Term.lam (atom (np (subjOfVerb (i + 1)))) (build n d (i + 1) (by omega))).HypLinear :=
      ⟨ih.1 L (by simp [L]), ih.2⟩
    refine ⟨fun k hk ↦ ?_, by
      simp only [build, Term.HypLinear]; exact ⟨⟨⟨trivial, hlam.rename _⟩, trivial⟩, trivial⟩⟩
    rw [hlen] at hk
    simp only [build, Term.uses, Term.uses_rename, hlen, ← hL]
    have hmap : ((build n d (i + 1) (by omega)).uses.map (liftPos L (L + 3) (· + 2))).count k =
        if 2 ≤ k ∧ k < L + 2 then 1 else 0 := by
      split_ifs with hk2
      · obtain ⟨u, rfl⟩ : ∃ u, k = u + 2 := ⟨k - 2, by omega⟩
        rw [show u + 2 = liftPos L (L + 3) (· + 2) u by simp [liftPos, show u < L by omega],
          List.count_map_of_injective _ _ hg]
        exact ih.1 u (by simp [← hL]; omega)
      · refine List.count_eq_zero.2 fun hmem ↦ ?_
        obtain ⟨u, _, hu⟩ := List.mem_map.1 hmem
        simp only [liftPos] at hu; split_ifs at hu <;> omega
    simp only [List.count_append, hmap, List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

theorem derivable_of_complete_coherent {s : Spine} (hv : 1 ≤ s.verbs)
    (h : s.Complete ∧ s.Coherent) : Derivable (premises s) (atom (.clause 0)) := by
  obtain ⟨n, m⟩ := s
  obtain rfl : m = n + 1 := ((Spine.complete_and_coherent_iff _ hv).1 h).symm
  refine ⟨_, ?_, build n n 0 (by omega), build_linear n n 0 _⟩
  simp [premises, subjOfVerb]

/-- The meaning constructors of a spine have a linear proof of its clause exactly when the
    spine is complete and coherent. -/
theorem derivable_iff_complete_coherent (s : Spine) (hv : 1 ≤ s.verbs) :
    Derivable (premises s) (atom (.clause 0)) ↔ s.Complete ∧ s.Coherent :=
  ⟨complete_coherent_of_derivable hv, derivable_of_complete_coherent hv⟩

open BresnanEtAl1982 (dutch tree)

theorem derivable_dutch (n : ℕ) :
    Derivable (premises (Spine.ofTree (dutch n))) (atom (.clause 0)) :=
  derivable_of_complete_coherent (by simp [dutch]) (BresnanEtAl1982.dutch_wellFormed n)

theorem not_derivable_extra_verb_or_np :
    ¬ Derivable (premises (Spine.ofTree (tree 1 3))) (atom (.clause 0)) ∧
      ¬ Derivable (premises (Spine.ofTree (tree 2 2))) (atom (.clause 0)) :=
  ⟨fun h ↦ BresnanEtAl1982.extra_verb_incomplete (complete_coherent_of_derivable (by simp) h).1,
    fun h ↦ BresnanEtAl1982.extra_np_incoherent (complete_coherent_of_derivable (by simp) h).2⟩

/-! ### The paper's examples -/

/-- The meaning constructors a row's words contribute. -/
def lexicon? (r : Datum) : Option (List (List (GlueTy Label))) :=
  match r.language, r.feature? "premises" with
  | "stan1293", some "likes, alex, blake" => some alexLikesBlake
  | "stan1293", some "love, every, some" => some everybodyLovesSomebody
  | "finn1318", some "speaker, drink, water" => some finnish
  | "stan1293", some "speaker, drink, water" => some english
  | _, _ => none

/-- The number of words of a row's sentence, which are separated by single spaces. -/
def wordCount (r : Datum) : ℕ := (r.primaryText.toList.filter (· = ' ')).length + 1

theorem rows_lexicon : ∀ r ∈ Examples.all, ∃ lex ∈ lexicon? r, wordCount r = lex.length := by
  decide

end Asudeh2022
