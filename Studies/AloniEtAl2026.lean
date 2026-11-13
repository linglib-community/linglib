module

public import Linglib.Core.Data.Set.Sups
public import Linglib.Logic.Team.Inquisitive
public import Linglib.Logic.Truthmaker.Bilateral
public import Mathlib.Data.Fintype.Order

/-!
# Aloni, Baltag, van Benthem, Bezhanishvili and Knudstorp (2026): teams, truthmakers, translations

Bilateral state-based logic (BSL) evaluates a formula at a team, a set of classical valuations, by
support and antisupport. Modal information logic (MIL) is a classical modal logic of
join-semilattices, whose binary modality $\langle\mathrm{sup}\rangle$ is true at the joins of a
point satisfying each argument; truthmaker conjunction [is this modality](##TSFormula.den_tr) and
so is BSL's disjunction. An entailment [holds in BSL exactly when its translation
holds](##consequence_iff) in MIL over distributive semilattices, under a theory $\Gamma$ fixing the
behaviour of the letters, and [likewise for inquisitive logic](##inquisitive_consequence_iff). The
proof sends a point to the team of valuations defined by the points below it, which [carries a
translation to its formula](##mem_den_tr) because it [lifts splits of teams](##exists_sup_eq).
Distributivity [cannot be dropped](##M3.not_faithful).

## Implementation notes

Truth sets are mathlib's operations on `Set S`: $\langle\mathrm{sup}\rangle$ is `⊻`,
$\langle\mathrm{sup}^*\rangle$ is `supClosure`, and `MIL.P` is `upperClosure`, the inexact
verification of truthmaker semantics. Support and antisupport form a pair in the product bilattice
`⊙`, as do verifiers and falsifiers. The forth condition is proved from `Defines.of_le`, without
the paper's decomposition of a point into parts defining valuations; only the back condition and
the atomic cases use the decomposition. The fullness model is the whole powerset rather than that
of the team, since a translation inspects only the points below its point of evaluation.

## TODO

The fixed-point logic $\mu$MIL, the Boolean negation and dependence atoms of the further team
logics, the converse of `isClosed_regularClosure_den` (Anttila and Knudstorp's expressive
completeness), and the K3 variant whose map is the analogue of Birkhoff's.

## References

* [M. Aloni, A. Baltag, J. van Benthem, N. Bezhanishvili and S. B. Knudstorp, *Teams, Truthmakers,
  Translations* (2026)][aloni-etal-2026]
* [M. Aloni, *Logic and Conversation: The Case of Free Choice* (2022)][aloni-2022]
* [A. Anttila and S. B. Knudstorp, *Convex Team Logics* (2025)][anttila-knudstorp-2025]
* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
-/

@[expose] public section

open scoped SetFamily
open scoped Bilattice

namespace AloniEtAl2026

universe u

/-! ### Modal information logic -/

/-- The formulas of modal information logic with finite suprema over the letters `A`: the Boolean
connectives, the binary modality $\langle\mathrm{sup}\rangle$ and the modality
$\langle\mathrm{sup}^*\rangle$ for joins of nonempty finite sets. -/
inductive MIL (A : Type*) where
  | atom (a : A)
  | bot
  | not (φ : MIL A)
  | or (φ ψ : MIL A)
  | sup (φ ψ : MIL A)
  | supStar (φ : MIL A)

namespace MIL

variable {A S ι : Type*} [SemilatticeSup S] {V : A → Set S} {x : S} {φ ψ : MIL A}

/-- The points of a semilattice with valuation `V` at which a formula is true. -/
def den (V : A → Set S) : MIL A → Set S
  | atom a => V a
  | bot => ∅
  | not φ => (den V φ)ᶜ
  | or φ ψ => den V φ ∪ den V ψ
  | sup φ ψ => den V φ ⊻ den V ψ
  | supStar φ => supClosure (den V φ)

/-- `⊤` abbreviates `~⊥`. -/
def top : MIL A := not bot

/-- `φ ∧ ψ` abbreviates `~(~φ ∨ ~ψ)`. -/
def and (φ ψ : MIL A) : MIL A := not (or (not φ) (not ψ))

/-- `Pφ` abbreviates $\langle\mathrm{sup}\rangle\varphi\top$. -/
def P (φ : MIL A) : MIL A := sup φ top

/-- `Hφ` abbreviates `~P~φ`. -/
def H (φ : MIL A) : MIL A := not (P (not φ))

/-- The conjunction of a finite family of formulas. -/
noncomputable def iInf [Finite ι] (f : ι → MIL A) : MIL A :=
  let _ := Fintype.ofFinite ι
  ((Finset.univ : Finset ι).toList.map f).foldr and top

attribute [simp] den

@[simp] theorem mem_den_and : x ∈ den V (and φ ψ) ↔ x ∈ den V φ ∧ x ∈ den V ψ := by
  simp [and]

@[simp] theorem den_top : den V (top : MIL A) = Set.univ := by simp [top]

@[simp] theorem den_P : den V (P φ) = upperClosure (den V φ) := by
  simp [P, Set.sups_univ]

theorem mem_den_H : x ∈ den V (H φ) ↔ ∀ y ≤ x, y ∈ den V φ := by
  simp [H, mem_upperClosure, not_imp_comm]

@[simp] theorem mem_den_iInf [Finite ι] {f : ι → MIL A} :
    x ∈ den V (iInf f) ↔ ∀ i, x ∈ den V (f i) := by
  have (l : List (MIL A)) : x ∈ den V (l.foldr and top) ↔ ∀ φ ∈ l, x ∈ den V φ := by
    induction l with
    | nil => simp
    | cons φ l ih => simp [ih]
  simp [iInf, this]

end MIL

/-! ### Bilateral state-based logic -/

/-- The formulas of BSL over the proposition letters `Atom`. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  | bot
  | ne
  | neg (φ : Formula Atom)
  | disj (φ ψ : Formula Atom)
  | conj (φ ψ : Formula Atom)
  | diamond (φ : Formula Atom)

variable {Atom : Type u}

namespace Formula

variable [Fintype Atom]

/-- The bilateral meaning of a BSL formula: `pro` is the set of teams supporting it and `con` the
set of teams antisupporting it. A team supports `♦φ` when a nonempty subteam supports `φ`. -/
def den : Formula Atom → Team.TeamProperty (Atom → Bool) ⊙ Team.TeamProperty (Atom → Bool)
  | atom p => .mk (Team.flat (· p = true)) (Team.flat (· p = false))
  | bot => .mk {∅} Set.univ
  | ne => .mk Team.ne {∅}
  | neg φ => (φ.den)ᶜ
  | disj φ ψ => Team.disj φ.den ψ.den
  | conj φ ψ => Team.conj φ.den ψ.den
  | diamond φ => .mk ↑(upperClosure (φ.den.pro ∩ Team.ne)) φ.den.con

end Formula

/-! ### The translation -/

/-- The translations `p⁺` (for `b = true`) and `p⁻` (for `b = false`) of a proposition letter:
`H⟨sup*⟩p₊` and `H⟨sup*⟩p₋`. -/
def lit (p : Atom) (b : Bool) : MIL (Atom × Bool) := .H (.supStar (.atom (p, b)))

section Translation

variable [Fintype Atom]

/-- The translation `NE⁺` of the non-emptiness atom. -/
noncomputable def nePos : MIL (Atom × Bool) :=
  .iInf fun p ↦ .not (.and (lit p true) (lit p false))

/-- The translation `NE⁻` of the non-emptiness atom. -/
noncomputable def neNeg : MIL (Atom × Bool) :=
  .iInf fun p ↦ .and (lit p true) (lit p false)

/-- The conjunction of the two members of the theory $\Gamma$: `H(NE⁺ ∨ NE⁻)` excludes points
that glut on only some letters, and the second conjunct is translated excluded middle. -/
noncomputable def gamma : MIL (Atom × Bool) :=
  .and (.H (.or nePos neNeg)) (.iInf fun p ↦ .sup (lit p true) (lit p false))

mutual

/-- The translation `φ⁺`, for support. -/
noncomputable def Formula.trPos : Formula Atom → MIL (Atom × Bool)
  | .atom p => lit p true
  | .bot => neNeg
  | .ne => nePos
  | .neg φ => φ.trNeg
  | .disj φ ψ => .sup φ.trPos ψ.trPos
  | .conj φ ψ => .and φ.trPos ψ.trPos
  | .diamond φ => .P (.and nePos φ.trPos)

/-- The translation `φ⁻`, for antisupport. -/
noncomputable def Formula.trNeg : Formula Atom → MIL (Atom × Bool)
  | .atom p => lit p false
  | .bot => .top
  | .ne => neNeg
  | .neg φ => φ.trPos
  | .disj φ ψ => .and φ.trNeg ψ.trNeg
  | .conj φ ψ => .sup φ.trNeg ψ.trNeg
  | .diamond φ => φ.trNeg

end

end Translation

/-! ### Literals in a semilattice model -/

section Model

variable {S : Type*} [SemilatticeSup S] {V : Atom × Bool → Set S} {x y z w : S} {p : Atom}
  {b : Bool} {v : Atom → Bool}

open MIL (den)

theorem mem_den_lit : x ∈ den V (lit p b) ↔ ∀ y ≤ x, y ∈ supClosure (V (p, b)) := by
  simp [lit, MIL.mem_den_H]

theorem isLowerSet_den_lit : IsLowerSet (den V (lit p b)) := fun _ _ hba ha ↦
  mem_den_lit.2 fun z hz ↦ mem_den_lit.1 ha z (hz.trans hba)

-- Lemma 4.5
theorem supClosed_den_lit [IsDistribSemilatticeSup S] : SupClosed (den V (lit p b)) := by
  have : den V (lit p b) = {x | ∀ y ≤ x, y ∈ supClosure (V (p, b))} := Set.ext fun _ ↦ mem_den_lit
  exact this ▸ supClosed_supClosure.setOf_forall_le

/-- `Defines V y v` says that the point `y` defines the classical valuation `v` (Definition 4.2). -/
def Defines (V : Atom × Bool → Set S) (y : S) (v : Atom → Bool) : Prop :=
  ∀ p b, y ∈ den V (lit p b) ↔ v p = b

theorem Defines.mem_den_lit (h : Defines V y v) (p : Atom) : y ∈ den V (lit p (v p)) :=
  (h p _).2 rfl

section Finite

variable [Fintype Atom]

open scoped Classical in
/-- The model transformation `G` sends a point to the team of the valuations defined by the points
below it (Definition 4.3). -/
noncomputable def G (V : Atom × Bool → Set S) (x : S) : Finset (Atom → Bool) :=
  Finset.univ.filter fun v ↦ ∃ y ≤ x, Defines V y v

@[simp] theorem mem_G : v ∈ G V x ↔ ∃ y ≤ x, Defines V y v := by simp [G]

theorem G_mono : Monotone (G V) := fun _ _ h _ hv ↦
  let ⟨w, hw, hd⟩ := mem_G.1 hv
  mem_G.2 ⟨w, hw.trans h, hd⟩

theorem mem_den_nePos :
    x ∈ den V nePos ↔ ∀ p, ¬ (x ∈ den V (lit p true) ∧ x ∈ den V (lit p false)) := by
  simp [nePos]

theorem mem_den_neNeg :
    x ∈ den V neNeg ↔ ∀ p, x ∈ den V (lit p true) ∧ x ∈ den V (lit p false) := by
  simp [neNeg]

theorem mem_den_gamma : x ∈ den V gamma ↔ (∀ y ≤ x, y ∈ den V nePos ∨ y ∈ den V neNeg) ∧
    ∀ p, x ∈ den V (lit p true) ⊻ den V (lit p false) := by
  simp [gamma, MIL.mem_den_H]

theorem isLowerSet_den_neNeg : IsLowerSet (den V neNeg) := fun _ _ hba ha ↦
  mem_den_neNeg.2 fun p ↦ ⟨isLowerSet_den_lit hba (mem_den_neNeg.1 ha p).1,
    isLowerSet_den_lit hba (mem_den_neNeg.1 ha p).2⟩

-- under $\Gamma$, a point at which some letter gluts simulates the empty team
private theorem mem_den_neNeg_of_glut (hx : x ∈ den V gamma) (h₁ : x ∈ den V (lit p true))
    (h₂ : x ∈ den V (lit p false)) : x ∈ den V neNeg :=
  ((mem_den_gamma.1 hx).1 x le_rfl).resolve_left fun h ↦ mem_den_nePos.1 h p ⟨h₁, h₂⟩

theorem Defines.notMem_den_neNeg [Nonempty Atom] (h : Defines V y v) : y ∉ den V neNeg :=
    fun hy ↦ by
  obtain ⟨p⟩ := ‹Nonempty Atom›
  have h₁ := (h p true).1 (mem_den_neNeg.1 hy p).1
  have h₂ := (h p false).1 (mem_den_neNeg.1 hy p).2
  exact absurd (h₁.symm.trans h₂) (by simp)

-- a point below a point defining `v` that does not simulate the empty team also defines `v`
private theorem Defines.of_le (h : Defines V w v) (hle : y ≤ w) (hy : y ∈ den V gamma)
    (hne : y ∉ den V neNeg) : Defines V y v := by
  refine fun p b ↦ ⟨fun hb ↦ ?_, fun hb ↦ isLowerSet_den_lit hle (hb ▸ h.mem_den_lit p)⟩
  by_contra hv
  have hc : y ∈ den V (lit p (!b)) :=
    Bool.eq_not_of_ne hv ▸ isLowerSet_den_lit hle (h.mem_den_lit p)
  cases b
  · exact hne (mem_den_neNeg_of_glut hy hc hb)
  · exact hne (mem_den_neNeg_of_glut hy hb hc)

theorem G_eq_empty [Nonempty Atom] (hy : y ∈ den V neNeg) : G V y = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hv ↦
    let ⟨_, hw, hd⟩ := mem_G.1 hv
    hd.notMem_den_neNeg (isLowerSet_den_neNeg hw hy)

section Distrib

variable [IsDistribSemilatticeSup S]

-- Lemma 4.6, second part
theorem isLowerSet_den_gamma : IsLowerSet (den V gamma) := fun _ _ hba ha ↦
  mem_den_gamma.2 ⟨fun z hz ↦ (mem_den_gamma.1 ha).1 z (hz.trans hba), fun p ↦
    (isLowerSet_den_lit.sups isLowerSet_den_lit) hba ((mem_den_gamma.1 ha).2 p)⟩

theorem supClosed_den_neNeg : SupClosed (den V neNeg) := fun _ ha _ hb ↦
  mem_den_neNeg.2 fun p ↦ ⟨supClosed_den_lit (mem_den_neNeg.1 ha p).1 (mem_den_neNeg.1 hb p).1,
    supClosed_den_lit (mem_den_neNeg.1 ha p).2 (mem_den_neNeg.1 hb p).2⟩

-- Lemma 4.8, first two items
theorem mem_supClosure_defines (hx : x ∈ den V gamma) (hne : x ∉ den V neNeg) :
    x ∈ supClosure {y | y ≤ x ∧ ∃ v, Defines V y v} := by
  classical
  let Good (s : Finset Atom) : Set S := {y | y ≤ x ∧ y ∉ den V neNeg ∧
    ∀ p ∈ s, y ∈ den V (lit p true) ∨ y ∈ den V (lit p false)}
  have step (s : Finset Atom) (p : Atom) : Good s ⊆ supClosure (Good (insert p s)) := by
    rintro y ⟨hyx, hyn, hys⟩
    have hdown {a : S} (ha : a ≤ y) (haN : a ∉ den V neNeg)
        (hap : a ∈ den V (lit p true) ∨ a ∈ den V (lit p false)) : a ∈ Good (insert p s) :=
      ⟨ha.trans hyx, haN, fun q hq ↦ (Finset.mem_insert.1 hq).elim (· ▸ hap) fun hq ↦
        (hys q hq).imp (isLowerSet_den_lit ha ·) (isLowerSet_den_lit ha ·)⟩
    by_cases hp : y ∈ den V (lit p true) ∨ y ∈ den V (lit p false)
    · exact subset_supClosure (hdown le_rfl hyn hp)
    · -- Lemma 4.7
      obtain ⟨hp₁, hp₂⟩ := not_or.1 hp
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.1
        ((mem_den_gamma.1 (isLowerSet_den_gamma hyx hx)).2 p)
      have ha' : a ∉ den V (lit p false) := fun h ↦ hp₂ (supClosed_den_lit h hb)
      have hb' : b ∉ den V (lit p true) := fun h ↦ hp₁ (supClosed_den_lit ha h)
      exact sup_mem_supClosure
        (hdown le_sup_left (fun h ↦ ha' (mem_den_neNeg.1 h p).2) (.inl ha))
        (hdown le_sup_right (fun h ↦ hb' (mem_den_neNeg.1 h p).1) (.inr hb))
  have hall (s : Finset Atom) : x ∈ supClosure (Good s) := by
    induction s using Finset.induction_on with
    | empty => exact subset_supClosure ⟨le_rfl, hne, by simp⟩
    | insert p s _ ih => exact supClosure_min (step s p) supClosed_supClosure ih
  have hsub : Good Finset.univ ⊆ {y | y ≤ x ∧ ∃ v, Defines V y v} := by
    rintro y ⟨hyx, hyn, hy⟩
    refine ⟨hyx, fun p ↦ decide (y ∈ den V (lit p true)), fun p b ↦ ?_⟩
    have hnot : ¬ (y ∈ den V (lit p true) ∧ y ∈ den V (lit p false)) := fun ⟨h₁, h₂⟩ ↦
      hyn (mem_den_neNeg_of_glut (isLowerSet_den_gamma hyx hx) h₁ h₂)
    have hor := hy p (Finset.mem_univ p)
    cases b <;> by_cases h : y ∈ den V (lit p true) <;> simp_all
  exact supClosure_mono hsub (hall _)

-- the atomic case of Lemma 4.11
theorem mem_den_lit_iff_G_mem (hy : y ∈ den V gamma) :
    y ∈ den V (lit p b) ↔ G V y ∈ Team.flat (· p = b) := by
  refine ⟨fun h v hv ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw, hd⟩ := mem_G.1 hv
    exact (hd p b).1 (isLowerSet_den_lit hw h)
  · by_cases hn : y ∈ den V neNeg
    · cases b
      exacts [(mem_den_neNeg.1 hn p).2, (mem_den_neNeg.1 hn p).1]
    · have hsub : {u | u ≤ y ∧ ∃ v, Defines V u v} ⊆ den V (lit p b) := fun w ⟨hw, v, hd⟩ ↦
        (hd p b).2 (h v (mem_G.2 ⟨w, hw, hd⟩))
      exact supClosure_min hsub supClosed_den_lit (mem_supClosure_defines hy hn)

variable [Nonempty Atom]

-- Lemma 4.6, first part
theorem exists_le_mem_den_neNeg (hx : x ∈ den V gamma) : ∃ y ≤ x, y ∈ den V neNeg := by
  obtain ⟨p⟩ := ‹Nonempty Atom›
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.1 ((mem_den_gamma.1 hx).2 p)
  obtain ⟨c, hca, hcb⟩ := exists_le_le a b
  have hc : c ≤ a ⊔ b := le_sup_of_le_left hca
  exact ⟨c, hc, mem_den_neNeg_of_glut (isLowerSet_den_gamma hc hx) (isLowerSet_den_lit hca ha)
    (isLowerSet_den_lit hcb hb)⟩

-- Lemma 4.9
theorem G_sup (hx : y ⊔ z ∈ den V gamma) : G V (y ⊔ z) = G V y ∪ G V z := by
  refine (Finset.union_subset (G_mono le_sup_left) (G_mono le_sup_right)).antisymm' fun v hv ↦ ?_
  obtain ⟨w, hw, hd⟩ := mem_G.1 hv
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_sup_eq_of_le_sup hw
  have hreg := isLowerSet_den_gamma hw hx
  by_cases han : a ∈ den V neNeg
  · have hbn : b ∉ den V neNeg := fun hbn ↦ hd.notMem_den_neNeg (supClosed_den_neNeg han hbn)
    exact Finset.mem_union_right _ <| mem_G.2
      ⟨b, hb, hd.of_le le_sup_right (isLowerSet_den_gamma le_sup_right hreg) hbn⟩
  · exact Finset.mem_union_left _ <| mem_G.2
      ⟨a, ha, hd.of_le le_sup_left (isLowerSet_den_gamma le_sup_left hreg) han⟩

theorem G_eq_singleton (hw : w ∈ den V gamma) (hd : Defines V w v) : G V w = {v} := by
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨mem_G.2 ⟨w, le_rfl, hd⟩, fun u hu ↦ ?_⟩
  obtain ⟨y, hy, hyd⟩ := mem_G.1 hu
  have := hd.of_le hy (isLowerSet_den_gamma hy hw) hyd.notMem_den_neNeg
  exact funext fun p ↦ (hyd p _).1 (this.mem_den_lit p)

theorem exists_G_eq (hx : x ∈ den V gamma) {s : Finset (Atom → Bool)} (hs : s ⊆ G V x) :
    ∃ y ≤ x, G V y = s := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨y, hy, hn⟩ := exists_le_mem_den_neNeg hx
    exact ⟨y, hy, G_eq_empty hn⟩
  | insert v s _ ih =>
    obtain ⟨y, hy, rfl⟩ := ih ((Finset.subset_insert _ _).trans hs)
    obtain ⟨w, hw, hd⟩ := mem_G.1 (hs (Finset.mem_insert_self _ _))
    have hle : y ⊔ w ≤ x := sup_le hy hw
    refine ⟨y ⊔ w, hle, ?_⟩
    rw [G_sup (isLowerSet_den_gamma hle hx), G_eq_singleton (isLowerSet_den_gamma hw hx) hd,
      Finset.union_comm, Finset.singleton_union]

/-- Lemma 4.10: a split of the team of a point lifts to a split of the point. -/
theorem exists_sup_eq (hx : x ∈ den V gamma) {s t : Finset (Atom → Bool)}
    (h : G V x = s ∪ t) : ∃ y z, y ⊔ z = x ∧ G V y = s ∧ G V z = t := by
  obtain ⟨y₁, hy₁, rfl⟩ := exists_G_eq hx (h ▸ Finset.subset_union_left : s ⊆ G V x)
  obtain ⟨z₁, hz₁, rfl⟩ := exists_G_eq hx (h ▸ Finset.subset_union_right : t ⊆ G V x)
  have hreg {u : S} (hu : u ≤ x) := isLowerSet_den_gamma hu hx
  by_cases hn : x ∈ den V neNeg
  · have hG := Finset.union_eq_empty.1 (h.symm.trans (G_eq_empty hn))
    exact ⟨x, x, sup_idem x, (G_eq_empty hn).trans hG.1.symm, (G_eq_empty hn).trans hG.2.symm⟩
  · let B (s : Finset (Atom → Bool)) : Set S := {u | u ≤ x ∧ G V u ⊆ s}
    have hB (s : Finset (Atom → Bool)) : SupClosed (B s) := fun a ha b hb ↦ by
      refine ⟨sup_le ha.1 hb.1, ?_⟩
      rw [G_sup (hreg (sup_le ha.1 hb.1))]
      exact Finset.union_subset ha.2 hb.2
    have hD : {u | u ≤ x ∧ ∃ v, Defines V u v} ⊆ B (G V y₁) ⊻ B (G V z₁) := by
      rintro u ⟨hu, v, hd⟩
      obtain ⟨e, he, hen⟩ := exists_le_mem_den_neNeg (hreg hu)
      have hE (s : Finset (Atom → Bool)) : e ∈ B s := ⟨he.trans hu, by simp [G_eq_empty hen]⟩
      have hv : v ∈ G V y₁ ∪ G V z₁ := h ▸ mem_G.2 ⟨u, hu, hd⟩
      rcases Finset.mem_union.1 hv with hv | hv
      · exact Set.mem_sups.2 ⟨u, ⟨hu, by simpa [G_eq_singleton (hreg hu) hd] using hv⟩, e, hE _,
          sup_eq_left.2 he⟩
      · exact Set.mem_sups.2 ⟨e, hE _, u, ⟨hu, by simpa [G_eq_singleton (hreg hu) hd] using hv⟩,
          sup_eq_right.2 he⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sups.1 <|
      supClosure_min hD ((hB _).sups (hB _)) (mem_supClosure_defines hx hn)
    refine ⟨a ⊔ y₁, b ⊔ z₁, ?_, ?_, ?_⟩
    · rw [sup_sup_sup_comm, hab]
      exact sup_eq_left.2 (sup_le hy₁ hz₁)
    · rw [G_sup (hreg (sup_le ha.1 hy₁))]
      exact Finset.union_eq_right.2 ha.2
    · rw [G_sup (hreg (sup_le hb.1 hz₁))]
      exact Finset.union_eq_right.2 hb.2

theorem mem_den_neNeg_iff_G_eq_empty (hy : y ∈ den V gamma) : y ∈ den V neNeg ↔ G V y = ∅ := by
  refine ⟨G_eq_empty, fun h ↦ ?_⟩
  by_contra hn
  obtain ⟨T, ⟨w, hw⟩, hTs, -⟩ := mem_supClosure_defines hy hn
  obtain ⟨hwy, v, hd⟩ := hTs hw
  exact Finset.notMem_empty v (h ▸ mem_G.2 ⟨w, hwy, hd⟩)

theorem mem_den_nePos_iff_G_nonempty (hy : y ∈ den V gamma) :
    y ∈ den V nePos ↔ (G V y).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, ← not_congr (mem_den_neNeg_iff_G_eq_empty hy)]
  refine ⟨fun h hn ↦ ?_, fun h ↦ ((mem_den_gamma.1 hy).1 y le_rfl).resolve_right h⟩
  obtain ⟨p⟩ := ‹Nonempty Atom›
  exact mem_den_nePos.1 h p (mem_den_neNeg.1 hn p)

-- the p-morphism property of `G` in the form the splitting clauses use
private theorem mem_sups_iff {A B : Set S} {A' B' : Set (Finset (Atom → Bool))}
    (hy : y ∈ den V gamma) (hA : ∀ z ∈ den V gamma, (z ∈ A ↔ G V z ∈ A'))
    (hB : ∀ z ∈ den V gamma, (z ∈ B ↔ G V z ∈ B')) : y ∈ A ⊻ B ↔ G V y ∈ A' ⊻ B' :=
  Set.mem_sups_congr (r := fun z t ↦ z ∈ den V gamma ∧ G V z = t)
    (fun ⟨hz, h⟩ ↦ ⟨_, _, (G_sup hz).symm.trans h, ⟨isLowerSet_den_gamma le_sup_left hz, rfl⟩,
      ⟨isLowerSet_den_gamma le_sup_right hz, rfl⟩⟩)
    (fun ⟨hz, h⟩ ↦
      let ⟨a, b, hab, ha, hb⟩ := exists_sup_eq hz h
      ⟨a, b, hab, ⟨isLowerSet_den_gamma (hab ▸ le_sup_left) hz, ha⟩,
        ⟨isLowerSet_den_gamma (hab ▸ le_sup_right) hz, hb⟩⟩)
    (fun _ _ ⟨hz, h⟩ ↦ h ▸ hA _ hz) (fun _ _ ⟨hz, h⟩ ↦ h ▸ hB _ hz) ⟨hy, rfl⟩

/-- Lemma 4.11: under $\Gamma$, the translation of a formula is true at a point exactly when the
team of the point supports the formula, and likewise for antisupport. -/
theorem mem_den_tr (φ : Formula Atom) (hy : y ∈ den V gamma) :
    (y ∈ den V φ.trPos ↔ G V y ∈ φ.den.pro) ∧ (y ∈ den V φ.trNeg ↔ G V y ∈ φ.den.con) := by
  induction φ generalizing y with
  | atom p => exact ⟨mem_den_lit_iff_G_mem hy, mem_den_lit_iff_G_mem hy⟩
  | bot => exact ⟨mem_den_neNeg_iff_G_eq_empty hy, iff_of_true (by simp [Formula.trNeg]) trivial⟩
  | ne => exact ⟨mem_den_nePos_iff_G_nonempty hy, mem_den_neNeg_iff_G_eq_empty hy⟩
  | neg φ ih => exact (ih hy).symm
  | disj φ ψ ih₁ ih₂ =>
    exact ⟨mem_sups_iff hy (fun _ hz ↦ (ih₁ hz).1) fun _ hz ↦ (ih₂ hz).1,
      MIL.mem_den_and.trans (and_congr (ih₁ hy).2 (ih₂ hy).2)⟩
  | conj φ ψ ih₁ ih₂ =>
    exact ⟨MIL.mem_den_and.trans (and_congr (ih₁ hy).1 (ih₂ hy).1),
      mem_sups_iff hy (fun _ hz ↦ (ih₁ hz).2) fun _ hz ↦ (ih₂ hz).2⟩
  | diamond φ ih =>
    refine ⟨?_, (ih hy).2⟩
    simp only [Formula.trPos, MIL.den_P, Formula.den, SetLike.mem_coe, mem_upperClosure]
    refine ⟨fun ⟨a, ha, hax⟩ ↦ ?_, fun ⟨s, ⟨hφ, hne⟩, hs⟩ ↦ ?_⟩
    · have hreg := isLowerSet_den_gamma hax hy
      obtain ⟨hne, hφ⟩ := MIL.mem_den_and.1 ha
      exact ⟨G V a, ⟨(ih hreg).1.1 hφ, (mem_den_nePos_iff_G_nonempty hreg).1 hne⟩, G_mono hax⟩
    · obtain ⟨a, ha, rfl⟩ := exists_G_eq hy hs
      have hreg := isLowerSet_den_gamma ha hy
      exact ⟨a, MIL.mem_den_and.2 ⟨(mem_den_nePos_iff_G_nonempty hreg).2 hne, (ih hreg).1.2 hφ⟩, ha⟩

end Distrib

end Finite

end Model

/-! ### The fullness model -/

section Fullness

variable [Fintype Atom]

open MIL (den)

/-- The valuation on the powerset of the valuations under which a letter holds of the teams that
give it the value (Definition 4.12). -/
def teamVal : Atom × Bool → Set (Finset (Atom → Bool)) := fun a ↦ Team.flat (· a.1 = a.2)

-- Lemma 4.13: on a powerset, the prefix `H⟨sup*⟩` fixes an ideal
@[simp] theorem den_lit_teamVal (p : Atom) (b : Bool) :
    den teamVal (lit p b) = Team.flat (· p = b) := by
  have hflat : Team.IsFlat (Team.flat fun v : Atom → Bool ↦ v p = b) := Team.isFlat_flat _
  ext t
  rw [mem_den_lit]
  change (∀ y ≤ t, y ∈ supClosure (Team.flat fun v : Atom → Bool ↦ v p = b)) ↔ _
  rw [hflat.supClosed.supClosure_eq]
  exact ⟨fun h ↦ h t le_rfl, fun h _ hy ↦ hflat.isLowerSet hy h⟩

-- Lemma 4.14, first part
theorem mem_den_gamma_teamVal (t : Finset (Atom → Bool)) : t ∈ den teamVal gamma := by
  refine mem_den_gamma.2 ⟨fun s _ ↦ ?_, fun p ↦ ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact .inr (mem_den_neNeg.2 fun p ↦ by simp)
    · refine .inl (mem_den_nePos.2 fun p ⟨h₁, h₂⟩ ↦ ?_)
      rw [den_lit_teamVal] at h₁ h₂
      exact absurd ((h₁ v hv).symm.trans (h₂ v hv)) (by simp)
  · simp only [den_lit_teamVal]
    refine Set.mem_sups.2 ⟨t.filter (· p = true), fun v hv ↦ (Finset.mem_filter.1 hv).2,
      t.filter (· p = false), fun v hv ↦ (Finset.mem_filter.1 hv).2, ?_⟩
    ext v
    cases hv : v p <;> simp [hv]

-- Lemma 4.14, second part
theorem G_teamVal [Nonempty Atom] (t : Finset (Atom → Bool)) : G teamVal t = t := by
  ext v
  refine mem_G.trans ⟨fun ⟨y, hy, hd⟩ ↦ hy ?_, fun hv ↦ ⟨{v}, Finset.singleton_subset_iff.2 hv,
    fun p b ↦ by simp⟩⟩
  have hd' (p : Atom) (b : Bool) : y ∈ Team.flat (· p = b) ↔ v p = b := by
    rw [← den_lit_teamVal]
    exact hd p b
  rcases y.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  · exact absurd (mem_den_neNeg.2 fun p ↦ by simp) hd.notMem_den_neNeg
  · exact (funext fun p ↦ (hd' p (v p)).2 rfl w hw : w = v) ▸ hw

/-- Theorem 4.15: an entailment holds in BSL exactly when its translation holds under $\Gamma$ in
every distributive semilattice model. -/
theorem consequence_iff [Nonempty Atom] (φ ψ : Formula Atom) :
    φ.den.pro ⊆ ψ.den.pro ↔
      ∀ (S : Type u) [SemilatticeSup S] [IsDistribSemilatticeSup S] (V : Atom × Bool → Set S),
        den V gamma ∩ den V φ.trPos ⊆ den V ψ.trPos := by
  refine ⟨fun h S _ _ V x ⟨hΓ, hφ⟩ ↦ (mem_den_tr ψ hΓ).1.2 (h ((mem_den_tr φ hΓ).1.1 hφ)),
    fun h t ht ↦ ?_⟩
  have hΓ := mem_den_gamma_teamVal t
  have key (χ : Formula Atom) : t ∈ den teamVal χ.trPos ↔ t ∈ χ.den.pro := by
    simpa only [G_teamVal] using (mem_den_tr χ hΓ).1
  exact (key ψ).1 (h _ teamVal ⟨hΓ, (key φ).2 ht⟩)

end Fullness

/-! ### Free choice and closure properties -/

section Closure

variable [Fintype Atom]

open Formula in
-- the free choice inference and its cancellation under negation, §3.1
theorem free_choice (α β : Formula Atom) :
    (diamond (disj (conj α ne) (conj β ne))).den.pro ⊆ (diamond α).den.pro ∧
      (neg (diamond (disj (conj α ne) (conj β ne)))).den.pro ⊆ (neg (diamond α)).den.pro := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨s, ⟨hs, -⟩, hst⟩ := mem_upperClosure.1 ht
    obtain ⟨a, ⟨haα, hane⟩, b, -, rfl⟩ := Set.mem_sups.1 hs
    exact mem_upperClosure.2 ⟨a, ⟨haα, hane⟩, le_sup_left.trans hst⟩
  · obtain ⟨a, ha, b, rfl, hab⟩ := Set.mem_sups.1 ht.1
    have hat : a = t := by simpa using hab
    exact hat ▸ ha

-- footnote 11: support and antisupport sets are weak ideals, closed under joins and convex
theorem supClosed_ordConnected_den (φ : Formula Atom) :
    (SupClosed φ.den.pro ∧ φ.den.pro.OrdConnected) ∧
      (SupClosed φ.den.con ∧ φ.den.con.OrdConnected) := by
  induction φ with
  | atom p =>
    exact ⟨⟨Team.supClosed_flat _, Team.ordConnected_flat _⟩, Team.supClosed_flat _,
      Team.ordConnected_flat _⟩
  | bot =>
    exact ⟨⟨Team.supClosed_singleton_empty, Team.ordConnected_singleton_empty⟩, supClosed_univ,
      Set.ordConnected_univ⟩
  | ne =>
    exact ⟨⟨Team.supClosed_ne, Team.ordConnected_ne⟩, Team.supClosed_singleton_empty,
      Team.ordConnected_singleton_empty⟩
  | neg φ ih => exact ⟨ih.2, ih.1⟩
  | disj φ ψ ih₁ ih₂ =>
    exact ⟨⟨ih₁.1.1.sups ih₂.1.1, ih₁.1.2.sups ih₂.1.2 ih₁.1.1 ih₂.1.1⟩,
      ih₁.2.1.inter ih₂.2.1, ih₁.2.2.inter ih₂.2.2⟩
  | conj φ ψ ih₁ ih₂ =>
    exact ⟨⟨ih₁.1.1.inter ih₂.1.1, ih₁.1.2.inter ih₂.1.2⟩,
      ih₁.2.1.sups ih₂.2.1, ih₁.2.2.sups ih₂.2.2 ih₁.2.1 ih₂.2.1⟩
  | diamond φ ih =>
    exact ⟨⟨fun a ha b _ ↦ (upperClosure _).upper le_sup_left ha,
      (upperClosure _).upper.ordConnected⟩, ih.2⟩

-- footnote 11: the support sets of BSL are regular propositions in Fine's sense
theorem isClosed_regularClosure_den [DecidableEq Atom] (φ : Formula Atom) :
    letI : CompleteLattice (Finset (Atom → Bool)) := Fintype.toCompleteLattice _
    Truthmaker.regularClosure.IsClosed φ.den.pro :=
  letI : CompleteLattice (Finset (Atom → Bool)) := Fintype.toCompleteLattice _
  Truthmaker.isClosed_regularClosure_iff_of_finite.2 (supClosed_ordConnected_den φ).1

end Closure

/-! ### Inquisitive logic -/

section Inquisitive

variable [Fintype Atom]

open MIL (den)

/-- The inquisitive model on the valuations; its modal component plays no role on modal-free
formulas (`Inquisitive.support_eq_of_isModalFree`). -/
def inqModel : Inquisitive.Model (Atom → Bool) Atom := ⟨fun _ ↦ ∅, fun p v ↦ v p = true⟩

/-- The translation of inquisitive logic, which sends implication to `H(φ⁺ → ψ⁺)` and inquisitive
disjunction to classical disjunction (§4.8). Modal formulas are sent to `⊥`, and the results on
them are not used. -/
noncomputable def inqTr : Inquisitive.Formula Atom → MIL (Atom × Bool)
  | .atom p => lit p true
  | .bot => neNeg
  | .conj φ ψ => .and (inqTr φ) (inqTr ψ)
  | .impl φ ψ => .H (.or (.not (inqTr φ)) (inqTr ψ))
  | .inqDisj φ ψ => .or (inqTr φ) (inqTr ψ)
  | .nec _ | .ent _ => .bot

variable [Nonempty Atom]

theorem mem_den_inqTr {S : Type*} [SemilatticeSup S] [IsDistribSemilatticeSup S]
    {V : Atom × Bool → Set S} {φ : Inquisitive.Formula Atom} (hφ : φ.IsModalFree) {y : S}
    (hy : y ∈ den V gamma) : y ∈ den V (inqTr φ) ↔ G V y ∈ Inquisitive.support inqModel φ := by
  induction φ generalizing y with
  | atom p => exact mem_den_lit_iff_G_mem hy
  | bot => exact (mem_den_neNeg_iff_G_eq_empty hy).trans (Inquisitive.mem_support_bot _ _).symm
  | conj φ ψ ih₁ ih₂ => exact MIL.mem_den_and.trans (and_congr (ih₁ hφ.1 hy) (ih₂ hφ.2 hy))
  | inqDisj φ ψ ih₁ ih₂ => exact or_congr (ih₁ hφ.1 hy) (ih₂ hφ.2 hy)
  | impl φ ψ ih₁ ih₂ =>
    simp only [inqTr, MIL.mem_den_H, MIL.den, Set.mem_union, Set.mem_compl_iff,
      Inquisitive.mem_support_impl]
    refine ⟨fun h t ht hφt ↦ ?_, fun h a ha ↦ ?_⟩
    · obtain ⟨a, ha, rfl⟩ := exists_G_eq hy ht
      have hreg := isLowerSet_den_gamma ha hy
      exact (ih₂ hφ.2 hreg).1 ((h a ha).resolve_left (not_not.2 ((ih₁ hφ.1 hreg).2 hφt)))
    · have hreg := isLowerSet_den_gamma ha hy
      by_cases hφa : a ∈ den V (inqTr φ)
      · exact .inr ((ih₂ hφ.2 hreg).2 (h _ (G_mono ha) ((ih₁ hφ.1 hreg).1 hφa)))
      · exact .inl hφa
  | nec _ => exact hφ.elim
  | ent _ => exact hφ.elim

/-- §4.8: an entailment between modal-free formulas holds in inquisitive logic exactly when its
translation holds under $\Gamma$ in every distributive semilattice model. -/
theorem inquisitive_consequence_iff {φ ψ : Inquisitive.Formula Atom} (hφ : φ.IsModalFree)
    (hψ : ψ.IsModalFree) :
    (Inquisitive.support inqModel φ : Set (Finset (Atom → Bool))) ⊆
        Inquisitive.support inqModel ψ ↔
      ∀ (S : Type u) [SemilatticeSup S] [IsDistribSemilatticeSup S] (V : Atom × Bool → Set S),
        den V gamma ∩ den V (inqTr φ) ⊆ den V (inqTr ψ) := by
  refine ⟨fun h S _ _ V x ⟨hΓ, hx⟩ ↦ (mem_den_inqTr hψ hΓ).2 (h ((mem_den_inqTr hφ hΓ).1 hx)),
    fun h t ht ↦ ?_⟩
  have hΓ := mem_den_gamma_teamVal t
  have key {χ : Inquisitive.Formula Atom} (hχ : χ.IsModalFree) :
      t ∈ den teamVal (inqTr χ) ↔ t ∈ Inquisitive.support inqModel χ := by
    simpa only [G_teamVal] using mem_den_inqTr hχ hΓ
  exact (key hψ).1 (h _ teamVal ⟨hΓ, (key hφ).2 ht⟩)

end Inquisitive

/-! ### Distributivity cannot be dropped -/

/-- The diamond lattice $M_3$. -/
inductive M3 where
  | bot | x | y | z | top
  deriving DecidableEq

namespace M3

instance : Max M3 := ⟨fun a b ↦ match a, b with
  | .bot, c | c, .bot => c
  | .x, .x => .x
  | .y, .y => .y
  | .z, .z => .z
  | _, _ => .top⟩

instance : SemilatticeSup M3 := SemilatticeSup.mk'
  (fun a b ↦ by cases a <;> cases b <;> rfl)
  (fun a b c ↦ by cases a <;> cases b <;> cases c <;> rfl)
  (fun a ↦ by cases a <;> rfl)

/-- The valuation of footnote 20. The footnote fixes only `V(p₊)`; `V(p₋) = {0, y}` makes $\Gamma$
true at the top. -/
def valuation : Unit × Bool → Set M3
  | (_, true) => {.bot, .x, .y}
  | (_, false) => {.bot, .y}

end M3

open MIL (den) in
/-- Footnote 20: the BSL entailment `p ∨ p ⊨ p` has a translation that fails under $\Gamma$ on the
non-distributive lattice $M_3$. -/
theorem M3.not_faithful :
    (Formula.disj (.atom ()) (.atom ())).den.pro ⊆ (Formula.atom ()).den.pro ∧
      ¬ den M3.valuation gamma ∩ den M3.valuation (Formula.disj (.atom ()) (.atom ())).trPos ⊆
        den M3.valuation (Formula.atom ()).trPos := by
  refine ⟨Set.sups_subset_self.2 (Team.isFlat_flat _).supClosed, fun h ↦ ?_⟩
  have key (a : M3) (b : Bool) (h : ∀ w, w ⊔ a = a → w ∈ M3.valuation ((), b)) :
      a ∈ den M3.valuation (lit () b) :=
    mem_den_lit.2 fun w hw ↦ subset_supClosure (h w (sup_eq_right.2 hw))
  obtain ⟨hxT, hyT, hyF⟩ : M3.x ∈ den M3.valuation (lit () true) ∧
      M3.y ∈ den M3.valuation (lit () true) ∧ M3.y ∈ den M3.valuation (lit () false) := by
    refine ⟨key .x true ?_, key .y true ?_, key .y false ?_⟩ <;>
      rintro (_ | _ | _ | _ | _) h <;> first | exact absurd h (by decide) | simp [M3.valuation]
  have hΓ : M3.top ∈ den M3.valuation gamma := by
    refine mem_den_gamma.2 ⟨fun w _ ↦ ?_, fun _ ↦ Set.mem_sups.2 ⟨.x, hxT, .y, hyF, rfl⟩⟩
    by_cases hw : w ∈ den M3.valuation (lit () true) ∧ w ∈ den M3.valuation (lit () false)
    · exact .inr (mem_den_neNeg.2 fun _ ↦ hw)
    · exact .inl (mem_den_nePos.2 fun _ ↦ hw)
  have hT : M3.top ∈ den M3.valuation (lit () true) :=
    h ⟨hΓ, Set.mem_sups.2 ⟨.x, hxT, .y, hyT, rfl⟩⟩
  have hclosed : SupClosed ({.bot, .x, .y, .top} : Set M3) := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  have hz := supClosure_min (t := ({.bot, .x, .y, .top} : Set M3))
    (fun w hw ↦ by
      simp only [M3.valuation, Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      tauto)
    hclosed (mem_den_lit.1 hT .z (sup_eq_right.1 rfl))
  simp at hz

/-! ### The truthmaker translation -/

/-- The formulas of propositional truthmaker logic. -/
inductive TSFormula (Atom : Type*) where
  | atom (p : Atom)
  | neg (φ : TSFormula Atom)
  | conj (φ ψ : TSFormula Atom)
  | disj (φ ψ : TSFormula Atom)

namespace TSFormula

variable {S : Type*} [SemilatticeSup S]

/-- The bilateral proposition a truthmaker formula expresses at a valuation `V = (V⁺, V⁻)`. -/
def den (V : Atom × Bool → Set S) : TSFormula Atom → Set S ⊙ Set S
  | atom p => .mk (V (p, true)) (V (p, false))
  | neg φ => (φ.den V)ᶜ
  | conj φ ψ => Truthmaker.conj (φ.den V) (ψ.den V)
  | disj φ ψ => Truthmaker.disj (φ.den V) (ψ.den V)

mutual

/-- The translation of truthmaking into modal information logic. -/
def trPos : TSFormula Atom → MIL (Atom × Bool)
  | atom p => .atom (p, true)
  | neg φ => φ.trNeg
  | conj φ ψ => .sup φ.trPos ψ.trPos
  | disj φ ψ => .or φ.trPos ψ.trPos

/-- The translation of falsemaking into modal information logic. -/
def trNeg : TSFormula Atom → MIL (Atom × Bool)
  | atom p => .atom (p, false)
  | neg φ => φ.trPos
  | conj φ ψ => .or φ.trNeg ψ.trNeg
  | disj φ ψ => .sup φ.trNeg ψ.trNeg

end

end TSFormula

-- Theorem 2.1: the translation of a truthmaker formula is true at its verifiers
theorem TSFormula.den_tr {S : Type*} [SemilatticeSup S] (V : Atom × Bool → Set S)
    (φ : TSFormula Atom) :
    MIL.den V φ.trPos = (φ.den V).pro ∧ MIL.den V φ.trNeg = (φ.den V).con := by
  induction φ with
  | atom p => exact ⟨rfl, rfl⟩
  | neg φ ih => exact ⟨ih.2, ih.1⟩
  | conj φ ψ ih₁ ih₂ | disj φ ψ ih₁ ih₂ =>
    simp [TSFormula.trPos, TSFormula.trNeg, TSFormula.den, ih₁.1, ih₁.2, ih₂.1, ih₂.2]

end AloniEtAl2026
