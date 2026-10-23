module

public import Mathlib.Order.FixedPoints
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.IntervalCases
public import Linglib.Phonology.Subregular.BMRS

/-!
# Yolyan and Comer (2026): Phonological Processes as Modal Transductions

Yolyan and Comer translate the modal μ-calculus on words into the Boolean monadic recursive
schemes of Bhaskar, Jardine, Chandlee and Oakden (`Subregular.BMRS`). Their main result
(Thm. 2) is that total BMRS programs and Kozen's μ-calculus express the same unary properties
of words, which gives an
alternative proof that order-preserving BMRS interpretations capture the rational functions.
`Formula` and `System` are the vectorial presentation of §4: a finite system of equations
`Xⱼ = θⱼ` whose semantics is the least fixed point of the induced monotone operator on
valuations. The translation `tr` (Def. 6) sends a right-hand side to a BMRS expression whose
rule heads are the recursion variables, and `eval_tr` is its compositionality (Remark 7):
wherever the rule-head calls agree with the recursion variables, `tr φ` evaluates to the truth
value of `φ`.

The paper's two worked examples run through both formalisms. Vowel nasalization, (2)–(4), is
non-recursive: `nasalization` is the program (3) and `nasalizationChi` the modal form (4), and
both mark the vowel of /bæn/ before the nasal (Fig. 3). Progressive nasal spreading in Warao,
(5)–(7), after Osborn, recurses under the backward modality: `warao` is the program (6),
`waraoChi` the modal form (7), and the two agree on the Fig. 4 and Fig. 5 columns of /naote/
(`warao_agreement`). Fig. 4 is the rounds of evaluating (6) (`warao_rounds`). Footnote 2 notes
that (3) ignores the word edge, so (3) has no value at a word-final vowel, while the
edge-guarded program is total (`not_totalOn_nasalization`, `nasalizationGuarded_totalOn`).
`warao_tr_agreement` runs Remark 7 on the translated Warao program, with the rule-head
hypothesis discharged by computation.

## Implementation notes

* Formulas are the negation-free fragment `μMLf+` of Thm. 8, extended with negated label atoms
  (`nlabel`); negation stays off the recursion variables, so monotonicity of the system operator
  is structural, while the Warao formula `N′ = μX.(N ∨ (¬T ∧ ♦X))` is expressible. Negated
  atoms translate as an if–then–else, the evident extension of the paper's clauses.
* Label atoms test the current symbol against a `Finset` class, since the paper's feature
  predicates N, V and T overlap (a nasalized vowel satisfies both V and N).
* The vectorial semantics is the least fixed point of the system operator by Knaster–Tarski,
  which by Bekić's theorem agrees with nested `μ`-binders.

## TODO

* Thm. 8, the translation of directed systems (Def. 3) by induction on the strongly connected
  components of the dependency graph, which discharges the hypothesis of `eval_tr`.
* The converse containment of Thm. 2 runs through monadic second-order logic and needs an MSO
  substrate.

## References

* [yolyan-comer-2026]
* [bhaskar-jardine-chandlee-oakden-2020]
* [kozen-1983]
* [osborn-1966]
-/

@[expose] public section

namespace YolyanComer2026

open Subregular Subregular.BMRS

variable {α : Type*} {n : ℕ}

/-! ### The vectorial modal μ-calculus on words (§4) -/

/-- Quantifier-free modal formulas over labels `α` and `n` recursion variables, negation-free
apart from the class atoms `nlabel`, so that recursion variables occur only positively.
`label` and `nlabel` test the current position's symbol against a `Finset` class; `initial` and
`final` are the edge tests `min` and `max`; `dia` (`◇`) reads the successor position and
`bdia` (`♦`) the predecessor. -/
inductive Formula (α : Type*) (n : ℕ) where
  | tru
  | fls
  | initial
  | final
  | label (s : Finset α)
  | nlabel (s : Finset α)
  | var (X : Fin n)
  | and (φ ψ : Formula α n)
  | or (φ ψ : Formula α n)
  | dia (φ : Formula α n)
  | bdia (φ : Formula α n)
  deriving DecidableEq

/-- Satisfaction at a pointed word `(w, i)` under a valuation `U` of the recursion
variables. -/
def Formula.Realize (w : List α) (U : Fin n → Set ℕ) : ℕ → Formula α n → Prop
  | _, .tru => True
  | _, .fls => False
  | i, .initial => i = 0
  | i, .final => i + 1 = w.length
  | i, .label s => ∃ a ∈ s, w[i]? = some a
  | i, .nlabel s => ∀ a ∈ s, w[i]? ≠ some a
  | i, .var X => i ∈ U X
  | i, .and φ ψ => φ.Realize w U i ∧ ψ.Realize w U i
  | i, .or φ ψ => φ.Realize w U i ∨ ψ.Realize w U i
  | i, .dia φ => ∃ j, succ? w i = some j ∧ φ.Realize w U j
  | i, .bdia φ => ∃ j, pred? w i = some j ∧ φ.Realize w U j

section RealizeSimp

variable {w : List α} {U : Fin n → Set ℕ} {i : ℕ} {s : Finset α} {φ ψ : Formula α n}

@[simp] theorem Formula.realize_tru : (Formula.tru : Formula α n).Realize w U i := trivial

@[simp] theorem Formula.realize_fls : ¬ (Formula.fls : Formula α n).Realize w U i :=
  not_false

@[simp] theorem Formula.realize_initial :
    (Formula.initial : Formula α n).Realize w U i ↔ i = 0 := .rfl

@[simp] theorem Formula.realize_final :
    (Formula.final : Formula α n).Realize w U i ↔ i + 1 = w.length := .rfl

@[simp] theorem Formula.realize_label :
    (Formula.label s : Formula α n).Realize w U i ↔ ∃ a ∈ s, w[i]? = some a := .rfl

@[simp] theorem Formula.realize_nlabel :
    (Formula.nlabel s : Formula α n).Realize w U i ↔ ∀ a ∈ s, w[i]? ≠ some a := .rfl

@[simp] theorem Formula.realize_var {X : Fin n} :
    (Formula.var X : Formula α n).Realize w U i ↔ i ∈ U X := .rfl

@[simp] theorem Formula.realize_and :
    (φ.and ψ).Realize w U i ↔ φ.Realize w U i ∧ ψ.Realize w U i := .rfl

@[simp] theorem Formula.realize_or :
    (φ.or ψ).Realize w U i ↔ φ.Realize w U i ∨ ψ.Realize w U i := .rfl

@[simp] theorem Formula.realize_dia :
    φ.dia.Realize w U i ↔ ∃ j, succ? w i = some j ∧ φ.Realize w U j := .rfl

@[simp] theorem Formula.realize_bdia :
    φ.bdia.Realize w U i ↔ ∃ j, pred? w i = some j ∧ φ.Realize w U j := .rfl

end RealizeSimp

instance Formula.instDecidableRealize [DecidableEq α] (w : List α)
    (U : Fin n → Set ℕ) [∀ X, DecidablePred (· ∈ U X)] :
    ∀ (i : ℕ) (φ : Formula α n), Decidable (φ.Realize w U i)
  | _, .tru => .isTrue trivial
  | _, .fls => .isFalse not_false
  | i, .initial => inferInstanceAs (Decidable (i = 0))
  | i, .final => inferInstanceAs (Decidable (i + 1 = w.length))
  | i, .label s => inferInstanceAs (Decidable (∃ a ∈ s, w[i]? = some a))
  | i, .nlabel s => inferInstanceAs (Decidable (∀ a ∈ s, w[i]? ≠ some a))
  | i, .var X => inferInstanceAs (Decidable (i ∈ U X))
  | i, .and φ ψ =>
      @instDecidableAnd _ _ (instDecidableRealize w U i φ) (instDecidableRealize w U i ψ)
  | i, .or φ ψ =>
      @instDecidableOr _ _ (instDecidableRealize w U i φ) (instDecidableRealize w U i ψ)
  | i, .dia φ =>
      match h : succ? w i with
      | none => .isFalse (by simp [Formula.realize_dia, h])
      | some j =>
          @decidable_of_iff _ _ (by simp [Formula.realize_dia, h])
            (instDecidableRealize w U j φ)
  | i, .bdia φ =>
      match h : pred? w i with
      | none => .isFalse (by simp [Formula.realize_bdia, h])
      | some j =>
          @decidable_of_iff _ _ (by simp [Formula.realize_bdia, h])
            (instDecidableRealize w U j φ)

theorem Formula.Realize.mono {w : List α} {U V : Fin n → Set ℕ} (hUV : U ≤ V) :
    ∀ {φ : Formula α n} {i : ℕ}, φ.Realize w U i → φ.Realize w V i
  | .tru, _, h => h
  | .fls, _, h => h
  | .initial, _, h => h
  | .final, _, h => h
  | .label _, _, h => h
  | .nlabel _, _, h => h
  | .var X, _, h => hUV X h
  | .and _ _, _, h => ⟨h.1.mono hUV, h.2.mono hUV⟩
  | .or _ _, _, h => h.imp (·.mono hUV) (·.mono hUV)
  | .dia _, _, ⟨j, hj, h⟩ => ⟨j, hj, h.mono hUV⟩
  | .bdia _, _, ⟨j, hj, h⟩ => ⟨j, hj, h.mono hUV⟩

/-- A vectorial formula is a finite system of equations `Xⱼ = θⱼ` with a designated
variable. -/
structure System (α : Type*) (n : ℕ) where
  /-- The right-hand side of each equation. -/
  eqs : Fin n → Formula α n
  /-- The designated variable whose satisfaction is the system's. -/
  out : Fin n

namespace System

variable (χ : System α n) (w : List α)

/-- The monotone operator a system induces on valuations. -/
def op : (Fin n → Set ℕ) →o (Fin n → Set ℕ) where
  toFun U X := {i | (χ.eqs X).Realize w U i}
  monotone' _ _ hUV _ _ h := h.mono hUV

@[simp] theorem mem_op {U : Fin n → Set ℕ} {X : Fin n} {i : ℕ} :
    i ∈ χ.op w U X ↔ (χ.eqs X).Realize w U i := .rfl

/-- The least-fixed-point valuation. -/
noncomputable def sem : Fin n → Set ℕ := OrderHom.lfp (χ.op w)

theorem op_sem : χ.op w (χ.sem w) = χ.sem w := (χ.op w).map_lfp

theorem sem_le {U : Fin n → Set ℕ} (hU : χ.op w U ≤ U) : χ.sem w ≤ U :=
  (χ.op w).lfp_le hU

/-- `w, i ⊨ χ` holds when the designated variable holds at `i` in the least fixed point. -/
def Sat (i : ℕ) : Prop := i ∈ χ.sem w χ.out

end System

/-- The single BMRS index variable. -/
abbrev x : Walk := .var

/-! ### Segments and feature classes -/

/-- Segments occurring in the paper's examples. -/
inductive Seg
  | n | a | o | t | e | b
  deriving DecidableEq, Repr

/-- The nasals, N. -/
def nas : Finset Seg := {.n}

/-- The vowels, V. -/
def vow : Finset Seg := {.a, .o, .e}

/-- The voiceless stops, T, which block spreading. -/
def stop : Finset Seg := {.t}

/-- /naote/, the Fig. 4 input. -/
def naote : List Seg := [.n, .a, .o, .t, .e]

/-- /bæn/, the vowel-nasalization input. -/
def baen : List Seg := [.b, .a, .n]

/-! ### Vowel nasalization ((2)–(4)): a vowel nasalizes before a nasal -/

/-- Output predicates of the nasalization program. -/
inductive NasHead
  | V' | N'
  deriving DecidableEq, Fintype

/-- The nasalization program (3), `V′(x) = V(x)` and `N′(x) = if V(x) then N(s(x)) else
N(x)`. -/
def nasalization : Program Seg NasHead
  | .V' => .label vow x
  | .N' => .ite (.label vow x) (.label nas x.succ) (.label nas x)

/-- On /bæn/ (Fig. 3) the output columns are V′ = ⊥⊤⊥ and N′ = ⊥⊤⊤, [bæ̃n], the æ nasalized
by the following n. -/
theorem nasalization_columns :
    (List.range 3).map (fun i ↦ nasalization.eval baen i (.call .V' x)) =
        [some false, some true, some false] ∧
      (List.range 3).map (fun i ↦ nasalization.eval baen i (.call .N' x)) =
        [some false, some true, some true] := by
  decide

/-- Program (3) ignores the word edge (footnote 2), so at a word-final vowel, where `s(x)`
denotes nothing, `N′` has no value. -/
theorem not_totalOn_nasalization : ¬ nasalization.TotalOn [.b, .a] := by decide

/-- The edge-guarded program of footnote 2, with `N′(x) = if V(x) then (if max(x) then N(x)
else N(s(x))) else N(x)`. -/
def nasalizationGuarded : Program Seg NasHead
  | .V' => .label vow x
  | .N' => .ite (.label vow x) (.ite (.final x) (.label nas x) (.label nas x.succ)) (.label nas x)

theorem nasalizationGuarded_totalOn (w : List Seg) : nasalizationGuarded.TotalOn w := by
  intro f i hi
  have hx : x.eval w i = some i := Walk.eval_var hi
  have hl := List.getElem?_eq_getElem hi
  have hb : Eval nasalizationGuarded w i (.label nas x) _ := .label hx hl
  cases f with
  | V' => exact ⟨_, .call hx (.label hx hl)⟩
  | N' =>
    by_cases hv : w[i] ∈ vow
    · rcases eq_or_ne i (w.length - 1) with hf | hf
      · exact ⟨_, .call hx (.ite_true (.label_true hx hl hv)
          (.ite_true (.final_true (hf ▸ hx)) hb))⟩
      · have hs : x.succ.eval w i = some (i + 1) := by
          rw [Walk.eval_succ_var, succ?_eq_some_iff]
          exact ⟨rfl, by omega⟩
        exact ⟨_, .call hx (.ite_true (.label_true hx hl hv) (.ite_false
          (.final_false hx (by omega)) (.label hs (List.getElem?_eq_getElem (by omega)))))⟩
    · exact ⟨_, .call hx (.ite_false (.label_false hx hl hv) hb)⟩

/-- The modal form (4), `N′ = (V ∧ ◇N) ∨ N`, which is not recursive. -/
def nasalizationChi : System Seg 1 where
  eqs _ := ((Formula.label vow).and (.dia (.label nas))).or (.label nas)
  out := 0

/-- The modal (4) marks exactly positions 1 and 2 of /bæn/ nasal, agreeing with the
BMRS N′ column. -/
theorem nasalizationChi_sat : ∀ i, nasalizationChi.Sat baen i ↔ i = 1 ∨ i = 2 := by
  intro i
  simp only [System.Sat]
  rw [← nasalizationChi.op_sem baen]
  match i with
  | 0 | 1 | 2 => simp [System.mem_op, nasalizationChi, vow, nas, baen, succ?]
  | k + 3 =>
    have hnone : baen[k + 3]? = none := List.getElem?_eq_none (by simp [baen])
    simp [System.mem_op, nasalizationChi, vow, nas, hnone,
      succ?_eq_some_iff]

/-! ### Warao nasal spreading ((5)–(7)): nasality spreads rightward until a stop -/

/-- The single output predicate of the spreading program. -/
inductive WHead
  | N'
  deriving DecidableEq, Fintype

/-- The spreading program (6), `N′(x) = if N(x) then ⊤ else if T(x) then ⊥ else if min(x)
then ⊥ else N′(p(x))`, recursive through the predecessor. -/
def warao : Program Seg WHead
  | .N' => .ite (.label nas x) .tru
      (.ite (.label stop x) .fls
        (.ite (.initial x) .fls (.call .N' x.pred)))

/-- Evaluating (6) on /naote/ in rounds reaches the output N′ = ⊤⊤⊤⊥⊥, [nãõte], as in Fig. 4. -/
theorem warao_rounds :
    (List.range 5).map (warao.approx naote 1 .N') = [some true, none, none, some false, none] ∧
    (List.range 5).map (warao.approx naote 2 .N') =
      [some true, some true, none, some false, some false] ∧
    (List.range 5).map (warao.approx naote 3 .N') =
      [some true, some true, some true, some false, some false] ∧
    (List.range 5).map (fun i ↦ warao.eval naote i (.call .N' x)) =
      [some true, some true, some true, some false, some false] := by
  decide

/-- The modal form (7), `N′ = μX.(N ∨ (¬T ∧ ♦X))`. -/
def waraoChi : System Seg 1 where
  eqs _ := (Formula.label nas).or ((Formula.nlabel stop).and (.bdia (.var 0)))
  out := 0

/-- The least fixed point on /naote/, where nasality holds exactly at positions 0, 1, 2. -/
abbrev waraoU : Fin 1 → Set ℕ := fun _ ↦ {i | i < 3}

theorem warao_op_le : waraoChi.op naote waraoU ≤ waraoU := by
  intro X i hi
  obtain rfl : X = 0 := Subsingleton.elim X 0
  simp only [System.mem_op, waraoChi, Formula.realize_or, Formula.realize_and,
    Formula.realize_label, Formula.realize_nlabel, Formula.realize_bdia,
    Formula.realize_var] at hi
  rcases hi with ⟨sg, hsg, hw⟩ | ⟨hT, j, hj, hj3⟩
  · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hw
    have hlt5 : i < 5 := by simpa [naote] using hlt
    have : i = 0 := by
      interval_cases i <;> simp_all [nas, naote]
    simp [this]
  · rw [pred?_eq_some_iff] at hj
    obtain ⟨rfl, hjlen⟩ := hj
    have hj3 : j < 3 := hj3
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · show j + 1 < 3
      omega
    · obtain rfl : j = 2 := by omega
      exact absurd rfl (hT .t (by decide) : naote[3]? ≠ some Seg.t)

theorem warao_le_sem : waraoU ≤ waraoChi.sem naote := by
  have hmem : ∀ i, waraoChi.sem naote 0 i =
      (waraoChi.eqs 0).Realize naote (waraoChi.sem naote) i := fun i ↦
    congrFun (congrFun (waraoChi.op_sem naote).symm 0) i
  have h0 : 0 ∈ waraoChi.sem naote 0 := by
    show waraoChi.sem naote 0 0
    rw [hmem]
    exact Or.inl ⟨.n, by decide, rfl⟩
  have h1 : 1 ∈ waraoChi.sem naote 0 := by
    show waraoChi.sem naote 0 1
    rw [hmem]
    exact Or.inr ⟨show ∀ sg ∈ stop, naote[1]? ≠ some sg by decide, 0, by decide, h0⟩
  have h2 : 2 ∈ waraoChi.sem naote 0 := by
    show waraoChi.sem naote 0 2
    rw [hmem]
    exact Or.inr ⟨show ∀ sg ∈ stop, naote[2]? ≠ some sg by decide, 1, by decide, h1⟩
  intro X i hi
  obtain rfl : X = 0 := Subsingleton.elim X 0
  have hi3 : i < 3 := hi
  interval_cases i
  exacts [h0, h1, h2]

theorem warao_sem : waraoChi.sem naote = waraoU :=
  le_antisymm (waraoChi.sem_le naote warao_op_le) warao_le_sem

/-- The modal (7) marks exactly positions 0, 1, 2 of /naote/ (Fig. 5). -/
theorem warao_sat {i : ℕ} : waraoChi.Sat naote i ↔ i < 3 := by
  rw [System.Sat, warao_sem]
  exact Iff.rfl

/-- The BMRS program (6) and the modal formula (7) compute the same nasality column on
/naote/, Fig. 4 and Fig. 5. -/
theorem warao_agreement (i : ℕ) (hi : i < 5) :
    Eval warao naote i (.call .N' x) true ↔ waraoChi.Sat naote i := by
  rw [warao_sat]
  interval_cases i <;> decide

/-! ### The translation (Def. 6) and its compositionality (Remark 7) -/

/-- The translation of Def. 6 sends a vectorial modal formula to a BMRS expression whose rule
heads are the recursion variables. Modalities substitute a moved term into the translated
body, and the connectives are the `if…then…else` forms of footnote 3. -/
def tr : Formula α n → Expr α (Fin n)
  | .tru => .tru
  | .fls => .fls
  | .initial => .initial x
  | .final => .final x
  | .label s => .label s x
  | .nlabel s => (Expr.label s x).not
  | .var X => .call X x
  | .and φ ψ => (tr φ).and (tr ψ)
  | .or φ ψ => (tr φ).or (tr ψ)
  | .dia φ => .ite (.final x) .fls ((tr φ).subst x.succ)
  | .bdia φ => .ite (.initial x) .fls ((tr φ).subst x.pred)

/-- The translated program of a system has one rule per recursion variable. -/
def System.trProgram (χ : System α n) : Program α (Fin n) := fun X ↦ tr (χ.eqs X)

/-- The translation is compositional (Remark 7). Wherever rule-head calls agree with the
recursion variables, `tr φ` evaluates to the truth value of `φ`. -/
theorem eval_tr [DecidableEq α] {P : Program α (Fin n)} {w : List α}
    {U : Fin n → Set ℕ} [∀ X, DecidablePred (· ∈ U X)]
    (hcall : ∀ X, ∀ j < w.length, Eval P w j (.call X x) (decide (j ∈ U X)))
    (φ : Formula α n) :
    ∀ {i : ℕ}, i < w.length → Eval P w i (tr φ) (decide (φ.Realize w U i)) := by
  induction φ with
  | tru => exact fun _ ↦ by simpa [tr] using (Eval.tru : Eval P w _ .tru true)
  | fls => exact fun _ ↦ by simpa [tr] using (Eval.fls : Eval P w _ .fls false)
  | initial => exact fun hi ↦ by simpa [tr] using Eval.initial (P := P) (Walk.eval_var hi)
  | final =>
    intro i hi
    have h : (Formula.final : Formula α n).Realize w U i ↔ i = w.length - 1 := by
      rw [Formula.realize_final]
      omega
    rw [decide_eq_decide.mpr h]
    exact Eval.final (Walk.eval_var hi)
  | label s =>
    intro i hi
    simpa [tr, List.getElem?_eq_getElem hi] using
      Eval.label (P := P) (s := s) (Walk.eval_var hi) (List.getElem?_eq_getElem hi)
  | nlabel s =>
    intro i hi
    simpa [tr, List.getElem?_eq_getElem hi] using
      (Eval.label (P := P) (s := s) (Walk.eval_var hi) (List.getElem?_eq_getElem hi)).not
  | var X => exact fun hi ↦ by simpa [tr] using hcall X _ hi
  | and φ ψ ihφ ihψ => exact fun hi ↦ by simpa [tr] using (ihφ hi).and (ihψ hi)
  | or φ ψ ihφ ihψ => exact fun hi ↦ by simpa [tr] using (ihφ hi).or (ihψ hi)
  | dia φ ih =>
    intro i hi
    by_cases h : i + 1 = w.length
    · rw [decide_eq_false (by
        simp only [Formula.realize_dia, succ?_eq_some_iff]
        rintro ⟨j, ⟨rfl, hj⟩, -⟩
        omega)]
      exact .ite_true (.final_true (by rw [Walk.eval_var hi]; congr 1; omega)) .fls
    · have hsucc : i + 1 < w.length := by omega
      rw [show decide (φ.dia.Realize w U i) = decide (φ.Realize w U (i + 1)) from
        decide_eq_decide.mpr (by simp [succ?_eq_some_iff, hsucc])]
      exact .ite_false (.final_false (Walk.eval_var hi) (by omega))
        (Eval.subst (by rw [Walk.eval_succ_var, succ?, ite_eq_left hsucc]) (ih hsucc))
  | bdia φ ih =>
    intro i hi
    by_cases h : i = 0
    · subst h
      rw [decide_eq_false (by
        simp only [Formula.realize_bdia, pred?_eq_some_iff]
        rintro ⟨j, ⟨hj, -⟩, -⟩
        omega)]
      exact .ite_true (.initial_true (by rw [Walk.eval_var hi])) .fls
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < w.length := by omega
      rw [show decide (φ.bdia.Realize w U (j + 1)) = decide (φ.Realize w U j) from
        decide_eq_decide.mpr (by simp [pred?_eq_some_iff, hj])]
      exact .ite_false (.initial_false (Walk.eval_var hi) (by omega))
        (Eval.subst (by rw [Walk.eval_pred_var hi]; simp [pred?, hj]) (ih hj))

theorem warao_tr_agreement (i : ℕ) (hi : i < 5) :
    Eval waraoChi.trProgram naote i (tr (waraoChi.eqs 0))
      (decide ((waraoChi.eqs 0).Realize naote waraoU i)) := by
  refine eval_tr (fun X j hj ↦ ?_) _ hi
  obtain rfl : X = 0 := Subsingleton.elim X 0
  have hj5 : j < 5 := by simpa [naote] using hj
  interval_cases j <;> decide

end YolyanComer2026
