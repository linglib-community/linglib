module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.Data.Set.Image
public import Linglib.Logic.PIP.Felicity
public import Linglib.Logic.PIP.Intensional
public import Linglib.Data.Examples.AbneyKeshet2025

/-!
# Abney and Keshet (2025): Plural Intensional Presuppositional predicate calculus (PIP)

The paper gives PIP a compositional fragment: indefinites, tense and determiner traces are
restricted variables, quantifier raising inserts summations labeled with a quantifier's restriction
and reference set, and modals and negation store their prejacent in a label. `interp` evaluates its
trees; on scenario models at a world of evaluation, [a pronoun anaphoric to a negated indefinite
is never true and felicitous](##judgment_139), [the bathroom disjunction presupposes at most one
bathroom](##felicitous_bathroom143_iff), [an indefinite read as a quantifier gives the strong
donkey reading](##realize_valuables116_sgIndef_iff), and [a presupposition is satisfied across
quantificational subordination](##felicitous_discourse150a_iff).

## Implementation notes

* Variables range over all pluralities; where the paper reads the variable `w` as a world, the
  assignment's value for it is a world by hypothesis.
* Singular restricted variables carry `SG`, as in the paper's bathroom sentence.
* The paper prints no translation of the European monarchies discourse. Ours follows its
  quantified sentences, with "their monarchs" a singular summation over each monarchy's monarchs.
* `IT` and `THEY` are not among the paper's defined constants; they presuppose `SG` and `PL`, as
  its singular and plural summation pronouns do.
* The `↑`-lift is defined on functions into formulas; on terms it is the identity, so `FX` on a
  function into terms drops the restricted variable's assertion.
* Label definitions nested in another's body are floated to the top of the discourse.

## TODO

* Of the paper's applications, only the paycheck and negated-indefinite pronouns, the bathroom
  disjunction, the valuables sentence and the European monarchies discourse are encoded.

## References

* [abney-keshet-2025]
* [keshet-abney-2024]
* [heim-kratzer-1998]
* [karttunen-1974-presupposition]
* [keshet-2018]
* [roberts-1987]
-/

@[expose] public section

namespace AbneyKeshet2025

open PIP

/-- The variables of the fragment: the world `w`, the modal-base world `u`, and the indices
of the paper's trees. -/
inductive Var
  | w | u | d | b | c | x | s | s' | e | t | m | k | v
  deriving DecidableEq

/-- Formula labels, as in the paper's trees and translations. -/
inductive Lab
  | B | S | M | U | W | O | X | K | C | A | L | V
  deriving DecidableEq

/-- Lexical relation symbols, by number of non-world arguments: the word senses of the
paper's examples. -/
inductive Lex : ℕ → Type
  | red : Lex 1
  | dog : Lex 1
  | barkEvt : Lex 1
  | hasAgent : Lex 2
  | hasPatient : Lex 2
  | student : Lex 1
  | umbrella : Lex 1
  | brought : Lex 3
  | useEvt : Lex 1
  | wolf : Lex 1
  | enters : Lex 1
  | car : Lex 1
  | owns : Lex 2
  | inShop : Lex 1
  | bathroom : Lex 1
  | here : Lex 1
  | funnyPlace : Lex 1
  | country : Lex 1
  | monarchy : Lex 1
  | monarchOf : Lex 2
  | cherish : Lex 2
  | fem : Lex 1
  | bring : Lex 2
  | person : Lex 1
  | valuable : Lex 1
  | lock : Lex 2

/-- Relation symbols: the lexical ones, accessibility between worlds, and the proportional
quantifier `most`. -/
inductive Sym : ℕ → Type
  | lex {n : ℕ} (c : Lex n) : Sym n
  | acc : Sym 1
  | most : Sym 2

/-- Terms of the fragment. -/
abbrev Tm := Term Var Lab Sym

/-- Formulas of the fragment. -/
abbrev Fm := Formula Var Lab Sym

/-- A one-place lexical predicate at the world `w`. -/
def pred₁ (c : Lex 1) (x : Tm) : Fm := .atom (.lex c) (.var .w) ![x]

/-- A two-place lexical predicate at the world `w`. -/
def pred₂ (c : Lex 2) (x y : Tm) : Fm := .atom (.lex c) (.var .w) ![x, y]

/-- A restricted variable: `[x] = x ∧ P(x)`, the common denotation of the indefinite
article, tense and the trace of a determiner (50). -/
def restricted (i : Var) (P : Tm → Fm) : Fm := .conj (.eq (.bvar i) (.var i)) (P (.var i))

/-! ### The metalanguage and the semantic operations -/

/-- Semantic types: individuals, worlds, truth values, functions. -/
inductive Ty
  | e | s | t
  | fn (σ τ : Ty)

/-- The metalanguage of the fragment: PIP terms at `e` and `s`, formulas at `t`, and
functions between them, as which the paper's λ-expressions are read. -/
def Sem : Ty → Type
  | .e => Tm
  | .s => Tm
  | .t => Fm
  | .fn σ τ => Sem σ → Sem τ

/-- `↑`-lifting (84): a function whose result is a formula takes an additional assertion,
conjoined to its result; the lift is the identity on terms. -/
def lift : {τ : Ty} → Sem τ → Fm → Sem τ
  | .e, x, _ => x
  | .s, x, _ => x
  | .t, ψ, φ => .conj ψ φ
  | .fn _ _, f, φ => fun a => lift (f a) φ

/-- Nonbranching nodes. -/
def NN {τ : Ty} (φ : Sem τ) : Sem τ := φ

/-- Functional application. -/
def FA {σ τ : Ty} (φ : Sem (.fn σ τ)) (ψ : Sem σ) : Sem τ := φ ψ

/-- Reverse functional application. -/
def AF {σ τ : Ty} (φ : Sem σ) (ψ : Sem (.fn σ τ)) : Sem τ := ψ φ

/-- Intensional functional application (82): the body is stored in the label `Z` and the
set of worlds satisfying it is the argument. -/
def IFA (Z : Lab) (φ : Tm → Fm) (ψ : Fm) : Fm := .conj (φ (.sigma .w (.label Z))) (.labelDef Z ψ)

/-- Application to a restricted variable: the lifted predicate takes the index and the
assertion. -/
def FX {τ : Ty} (P : Sem (.fn .e τ)) (i : Var) (φ : Fm) : Sem τ := lift (P (.var i)) φ

/-- Predicate modification. -/
def PM (φ ψ : Tm → Fm) : Tm → Fm := fun a => .conj (φ a) (ψ a)

/-- Predicate abstraction `λxφ`, reading through the labels `A` of the preceding
discourse before substituting for `x` (123). -/
def PA (A : List (Lab × Fm)) (i : Var) (φ : Fm) : Tm → Fm := fun t => Expr.subst i t (φ.expand A)

/-- Summation with a label: `ΣxZ where Z ≡ φ`, the definition attached to the use. -/
def SA (i : Var) (Z : Lab) (φ : Fm) : Tm := .sigma i (.conj (.label Z) (.labelDef Z φ))

/-! ### The lexicon -/

/-- Terminals: lexical predicates, thematic roles, determiners, pronouns, and the defined
constants (88) with their indices and labels. -/
inductive Word
  | pred (c : Lex 1)
  | role (c : Lex 2)
  | every
  | most
  | a (i : Var)
  | tense (i : Var)
  | dTrace (i : Var)
  | dpTrace (i : Var)
  | core (i : Var)
  | ldpTrace (Z : Lab)
  | she
  | it
  | they
  | not (Z : Lab)
  | might (Z : Lab)
  | must (Z : Lab)
  | base

/-- The semantic type of a terminal. -/
def Word.ty : Word → Ty
  | .pred _ => .fn .e .t
  | .role _ => .fn .e (.fn .e .t)
  | .every => .fn .e (.fn .e .t)
  | .most => .fn .e (.fn .e .t)
  | .a _ => .fn (.fn .e .t) .t
  | .tense _ => .fn (.fn .e .t) .t
  | .dTrace _ => .fn (.fn .e .t) .t
  | .dpTrace _ => .e
  | .core _ => .e
  | .ldpTrace _ => .t
  | .she => .fn .e .e
  | .it => .fn .e .e
  | .they => .fn .e .e
  | .not _ => .fn .s .t
  | .might _ => .fn .s (.fn .s .t)
  | .must _ => .fn .s (.fn .s .t)
  | .base => .s

/-- The meaning of a terminal (87)–(88): a thematic role `λxλe(HAS-ROLE(e, x))`, `EVERY` as
inclusion, the restricted variables `A_x`, `T_x`, `D-T_x`, the simple variables `DP-T_x`
and `E_x`, the label of a labeled trace, pronouns `λz(z|Q(z))`, negation `λψ(w ∉ ψ)`, the
modals as relations to the modal base, and the base `β_w`. -/
def Word.sem : (α : Word) → Sem α.ty
  | .pred c => fun a => pred₁ c a
  | .role c => fun a e => pred₂ c e a
  | .every => fun a b => .subset a b
  | .most => fun a b => .atom .most (.var .w) ![a, b]
  | .a i => restricted i
  | .tense i => restricted i
  | .dTrace i => restricted i
  | .dpTrace i => .var i
  | .core i => .var i
  | .ldpTrace Z => .label Z
  | .she => fun z => .presup z (.conj (pred₁ .fem z) (.sg z))
  | .it => fun z => .presup z (.sg z)
  | .they => fun z => .presup z (.pl z)
  | .not _ => fun ψ => .neg (.mem (.var .w) ψ)
  | .might _ => fun β ψ => Formula.some β ψ
  | .must _ => fun β ψ => .subset β ψ
  | .base => Term.modalBase .acc .w .u

/-! ### Trees and their interpretation -/

/-- An LF tree annotated with the semantic operation at each node (86), with the index of
a restricted variable and the label of a summation or intensional operator as data. -/
inductive Tree : Ty → Type
  | lex (α : Word) : Tree α.ty
  | nn {τ : Ty} (β : Tree τ) : Tree τ
  | fa {σ τ : Ty} (β : Tree (.fn σ τ)) (γ : Tree σ) : Tree τ
  | af {σ τ : Ty} (β : Tree σ) (γ : Tree (.fn σ τ)) : Tree τ
  | ifa (Z : Lab) (β : Tree (.fn .s .t)) (γ : Tree .t) : Tree .t
  | fx {τ : Ty} (β : Tree (.fn .e τ)) (i : Var) (γ : Tree .t) : Tree τ
  | pm (β γ : Tree (.fn .e .t)) : Tree (.fn .e .t)
  | pa (i : Var) (γ : Tree .t) : Tree (.fn .e .t)
  | sa (i : Var) (Z : Lab) (γ : Tree .t) : Tree .e

/-- The meaning of a tree, relative to the label definitions `A` of the preceding
discourse. -/
def interp (A : List (Lab × Fm)) : {τ : Ty} → Tree τ → Sem τ
  | _, .lex α => α.sem
  | _, .nn β => NN (interp A β)
  | _, .fa β γ => FA (interp A β) (interp A γ)
  | _, .af β γ => AF (interp A β) (interp A γ)
  | _, .ifa Z β γ => IFA Z (interp A β) (interp A γ)
  | _, .fx β i γ => FX (interp A β) i (interp A γ)
  | _, .pm β γ => PM (interp A β) (interp A γ)
  | _, .pa i γ => PA A i (interp A γ)
  | _, .sa i Z γ => SA i Z (interp A γ)

/-! ### The paper's trees -/

/-- (47): "a red dog barked". -/
def aRedDogBarked : Tree .t :=
  .fx (.fx (.lex (.role .hasAgent)) .d
      (.fa (.lex (.a .d)) (.pm (.lex (.pred .red)) (.lex (.pred .dog)))))
    .b (.fa (.lex (.tense .b)) (.nn (.lex (.pred .barkEvt))))

-- (91), (92), (47)
theorem interp_aRedDogBarked :
    interp [] aRedDogBarked =
      .conj (.conj (pred₂ .hasAgent (.var .b) (.var .d))
          (restricted .d fun x => .conj (pred₁ .red x) (pred₁ .dog x)))
        (restricted .b (pred₁ .barkEvt)) := rfl

/-- (92) abbreviated: `HAS-AGENT(b, d) ∧ RED([d]) ∧ DOG(d) ∧ BARK-EVT([b])`. -/
def form92 : Fm :=
  .conj (.conj (.conj (pred₂ .hasAgent (.var .b) (.var .d)) (pred₁ .red (.bvar .d)))
      (pred₁ .dog (.var .d)))
    (pred₁ .barkEvt (.bvar .b))

variable {W E : Type}

-- (47), (92)
theorem intersubstitutable_aRedDogBarked :
    (interp [] aRedDogBarked).Intersubstitutable (Atom W E) form92 := by
  rw [interp_aRedDogBarked]
  refine ⟨fun M g => ⟨?_, ?_⟩, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · simp only [Formula.realize_conj, Formula.realize_atom, Formula.realize_eq, restricted, pred₁,
      pred₂, form92, Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var,
      Term.realize_bvar, and_assoc, true_and]
  · simp only [Formula.felicitous_conj, Formula.felicitous_atom, Formula.felicitous_eq, restricted,
      pred₁, pred₂, form92, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      IsEmpty.forall_iff, Term.felicitous_var, Term.felicitous_bvar, and_self, implies_true]

-- fn. 7
theorem not_intersubstitutable_bvar_var (c : Lex 1) (i : Var) :
    ¬ (pred₁ c (.bvar i)).Intersubstitutable (Atom W E) (pred₁ c (.var i)) :=
  fun h => by simpa [pred₁, Expr.locals] using (h.2.1 i).1

-- (34), fn. 13
theorem not_intersubstitutable_conj_comm :
    ¬ ∀ φ ψ : Fm, Formula.Intersubstitutable (Atom W E) (φ.conj ψ) (ψ.conj φ) := fun h => by
  simpa using ((h (.neg .top) (.presup .top (.neg .top))).1 ⟨fun _ _ _ => False⟩ fun _ => ∅).2

/-- (118): the label definitions of "Almost every student brought an umbrella today",
`S ≡ STUDENT([s])`, `B ≡ (S ∧ UMBRELLA([u]) ∧ BROUGHT([b], s, u))`. -/
def defs118 : List (Lab × Fm) :=
  [(.S, restricted .s (pred₁ .student)),
   (.B, .conj (.label .S) (.conj (restricted .u (pred₁ .umbrella))
      (.atom (.lex .brought) (.var .w) ![.bvar .b, .var .s, .var .u])))]

/-- (121): "Most of them used it", the subordinate quantifier's restriction a labeled trace
of the preceding sentence abstracted by `PA` (122). -/
def mostOfThemUsedIt : Tree .t :=
  .fa (.fa (.lex .most)
      (.sa .s' .M (.fa (.lex (.dTrace .s')) (.pa .s (.lex (.ldpTrace .B))))))
    (.sa .s' .U (.fx (.fx (.lex (.role .hasAgent)) .s' (.lex (.ldpTrace .M))) .e
      (.fa (.lex (.tense .e)) (.pm (.lex (.pred .useEvt))
        (.fa (.lex (.role .hasPatient)) (.fa (.lex .it) (.lex (.core .u))))))))

-- (128), (127)
theorem interp_mostOfThemUsedIt :
    interp defs118 mostOfThemUsedIt =
      .atom .most (.var .w) ![
        SA .s' .M (restricted .s' fun y => .conj (.conj (.eq (.bvar .s') y) (pred₁ .student y))
          (.conj (restricted .u (pred₁ .umbrella))
            (.atom (.lex .brought) (.var .w) ![.bvar .b, y, .var .u]))),
        SA .s' .U (.conj (.conj (pred₂ .hasAgent (.var .e) (.var .s')) (.label .M))
          (restricted .e fun e => .conj (pred₁ .useEvt e)
            (pred₂ .hasPatient e (.presup (.var .u) (.sg (.var .u))))))] := rfl

/-- (132a): "A wolf might enter", the modal applied to the modal base and, by `IFA`, to the
worlds of its labeled prejacent. -/
def aWolfMightEnter : Tree .t :=
  .ifa .W (.fa (.lex (.might .W)) (.lex .base))
    (.fx (.lex (.pred .enters)) .x (.fa (.lex (.a .x)) (.lex (.pred .wolf))))

-- (133a), (82)
theorem interp_aWolfMightEnter :
    interp [] aWolfMightEnter =
      .conj (Formula.some (Term.modalBase .acc .w .u) (.sigma .w (.label .W)))
        (.labelDef .W (.conj (pred₁ .enters (.var .x)) (restricted .x (pred₁ .wolf)))) := rfl

/-! ### Scenarios -/

/-- A scenario: accessibility between worlds, the proportional relation interpreting `most`, and
the lexical relations among entities at each world. -/
structure Scenario (W E : Type) where
  acc : W → W → Prop
  most : Set (Atom W E) → Set (Atom W E) → Prop
  rel : ∀ {n : ℕ}, Lex n → W → (Fin n → E) → Prop

/-- The model of a scenario: the lexical symbols over pluralities of entities and accessibility
over pluralities of worlds, distributively, and `most` as the scenario's proportional relation. -/
def Scenario.model (S : Scenario W E) : Model Sym (Atom W E) where
  I r Wp ts := match r with
    | .lex c => (Model.intensional fun c w as => ∃ es, as = Sum.inr ∘ es ∧ S.rel c w es).I c Wp ts
    | .acc => ∃ w, Wp = world w ∧ (ts 0).Nonempty ∧ ts 0 ⊆ Sum.inl '' {u | S.acc w u}
    | .most => S.most (ts 0) (ts 1)

/-- Whether a relation symbol is lexical. -/
def Sym.isLex : ∀ {n : ℕ}, Sym n → Bool
  | _, .lex _ => true
  | _, _ => false

theorem Scenario.divisive (S : Scenario W E) {n : ℕ} (r : Sym n) (hr : r.isLex = true) :
    S.model.Divisive r := by
  cases r
  · exact Model.divisive_intensional (rel := fun c w as => ∃ es, as = Sum.inr ∘ es ∧ S.rel c w es) _
  all_goals simp [Sym.isLex] at hr

variable (S : Scenario W E) (h : Var → Set (Atom W E)) {w₀ : W} {x₀ : E}

theorem felicitous_pred₁ (c : Lex 1) (t : Tm) :
    (pred₁ c t).Felicitous S.model h ↔ t.Felicitous S.model h := by
  simp only [pred₁, Formula.felicitous_atom, Term.felicitous_var, Fin.forall_fin_one,
    Matrix.cons_val_zero, true_and]

theorem felicitous_pred₂ (c : Lex 2) (s t : Tm) :
    (pred₂ c s t).Felicitous S.model h ↔ s.Felicitous S.model h ∧ t.Felicitous S.model h := by
  simp only [pred₂, Formula.felicitous_atom, Term.felicitous_var, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, true_and]

theorem realize_mem_world (hw : h .w = world w₀) (t : Tm) :
    Formula.Realize S.model h (.mem (.var .w) t) ↔ Sum.inl w₀ ∈ t.realize S.model h := by
  simp only [Formula.realize_mem, Term.realize_var, hw, world, Set.singleton_eq_singleton_iff,
    exists_eq_left']

private theorem exists_comp_inr₁ {a : Atom W E} {P : (Fin 1 → E) → Prop} :
    (∃ es, ![a] = Sum.inr ∘ es ∧ P es) ↔ ∃ e, P ![e] ∧ Sum.inr e = a :=
  ⟨fun ⟨es, h, hp⟩ => ⟨es 0, by rwa [show ![es 0] = es from funext (Fin.forall_fin_one.2 rfl)],
    (congrFun h 0).symm⟩, fun ⟨_, hp, h⟩ => ⟨_, h ▸ funext (Fin.forall_fin_one.2 rfl), hp⟩⟩

private theorem exists_comp_inr₂ {a b : Atom W E} {P : (Fin 2 → E) → Prop} :
    (∃ es, ![a, b] = Sum.inr ∘ es ∧ P es) ↔ ∃ e e', a = .inr e ∧ b = .inr e' ∧ P ![e, e'] :=
  ⟨fun ⟨es, h, hp⟩ => ⟨es 0, es 1, congrFun h 0, congrFun h 1,
    by rwa [show ![es 0, es 1] = es from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]⟩,
    fun ⟨_, _, ha, hb, hp⟩ => ⟨_, ha ▸ hb ▸ funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩), hp⟩⟩

theorem realize_pred₁ (c : Lex 1) (t : Tm) :
    (pred₁ c t).Realize S.model h ↔ ∃ w, h .w = world w ∧ (t.realize S.model h).Nonempty ∧
      t.realize S.model h ⊆ Sum.inr '' {e | S.rel c w ![e]} := by
  simp only [pred₁, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
    Term.realize_var, Scenario.model, Model.intensional_apply₁, exists_comp_inr₁, Set.subset_def,
    Set.mem_image, Set.mem_ofPred_eq]

theorem realize_pred₂ (c : Lex 2) (s t : Tm) :
    (pred₂ c s t).Realize S.model h ↔ ∃ w, h .w = world w ∧ (s.realize S.model h).Nonempty ∧
      (t.realize S.model h).Nonempty ∧ ∀ a ∈ s.realize S.model h, ∀ b ∈ t.realize S.model h,
        ∃ e e', a = .inr e ∧ b = .inr e' ∧ S.rel c w ![e, e'] := by
  simp only [pred₂, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
    Term.realize_var, Scenario.model, Model.intensional_apply₂, exists_comp_inr₂]

/-! ### Singular indefinites -/

/-- `SG(i) ∧ c_w([i])`: a singular indefinite `[i]` of kind `c`. -/
def sgIndef (c : Lex 1) (i : Var) : Fm := .conj (.sg (.var i)) (pred₁ c (.bvar i))

/-- `SG(i) ∧ c_w([i]) ∧ c′_w(i)`: a singular indefinite with a further predicate. -/
def sgIndefWith (c c' : Lex 1) (i : Var) : Fm := .conj (sgIndef c i) (pred₁ c' (.var i))

theorem locals_sgIndef (c : Lex 1) (i : Var) : (sgIndef c i).locals = [i] := rfl

theorem locals_sgIndefWith (c c' : Lex 1) (i : Var) : (sgIndefWith c c' i).locals = [i] := rfl

theorem felicitous_sgIndef (c : Lex 1) (i : Var) : (sgIndef c i).Felicitous S.model h :=
  Expr.felicitous_of_presupFree _ _ (of_decide_eq_true rfl) _

theorem felicitous_sgIndefWith (c c' : Lex 1) (i : Var) :
    (sgIndefWith c c' i).Felicitous S.model h :=
  Expr.felicitous_of_presupFree _ _ (of_decide_eq_true rfl) _

theorem realize_sgIndef (c : Lex 1) (i : Var) (hw : h .w = world w₀) :
    Formula.Realize S.model h (sgIndef c i) ↔ ∃ e, h i = {Sum.inr e} ∧ S.rel c w₀ ![e] := by
  rw [sgIndef, Formula.realize_conj, Formula.realize_sg, realize_pred₁, Term.realize_var,
    Term.realize_bvar, hw]
  simp only [world_inj, exists_eq_left']
  constructor
  · rintro ⟨⟨a, ha⟩, -, hs⟩
    obtain ⟨e, he, rfl⟩ := hs (by rw [ha]; exact Set.mem_singleton _)
    exact ⟨e, ha, he⟩
  · rintro ⟨e, ha, he⟩
    rw [ha]
    exact ⟨⟨_, rfl⟩, Set.singleton_nonempty _, Set.singleton_subset_iff.2 ⟨e, he, rfl⟩⟩

theorem realize_sgIndefWith (c c' : Lex 1) (i : Var) (hw : h .w = world w₀) :
    Formula.Realize S.model h (sgIndefWith c c' i) ↔
      ∃ e, h i = {Sum.inr e} ∧ S.rel c w₀ ![e] ∧ S.rel c' w₀ ![e] := by
  rw [sgIndefWith, Formula.realize_conj, realize_sgIndef S h c i hw, realize_pred₁, hw,
    Term.realize_var]
  simp only [world_inj, exists_eq_left']
  constructor
  · rintro ⟨⟨e, ha, he⟩, -, hs⟩
    obtain ⟨e', he', hee⟩ := hs (by rw [ha]; exact Set.mem_singleton _)
    cases Sum.inr_injective hee
    exact ⟨e, ha, he, he'⟩
  · rintro ⟨e, ha, he, he'⟩
    rw [ha]
    exact ⟨⟨e, rfl, he⟩, Set.singleton_nonempty _, Set.singleton_subset_iff.2 ⟨e, he', rfl⟩⟩

theorem realize_sigma_sgIndef (c : Lex 1) {i : Var} (hi : i ≠ .w) (hw : h .w = world w₀) :
    Term.realize S.model h (.sigma i (sgIndef c i)) = Sum.inr '' {e | S.rel c w₀ ![e]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [locals_sgIndef]
  simp [sgIndef, realize_pred₁, hi.symm, hw, world_inj]

theorem realize_sigma_sgIndefWith (c c' : Lex 1) {i : Var} (hi : i ≠ .w) (hw : h .w = world w₀) :
    Term.realize S.model h (.sigma i (sgIndefWith c c' i)) =
      Sum.inr '' {e | S.rel c w₀ ![e] ∧ S.rel c' w₀ ![e]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [locals_sgIndefWith]
  rcases a with _ | e <;> simp [sgIndefWith, sgIndef, realize_pred₁, hi.symm, hw, world_inj]

/-! ### Paycheck pronouns and negation -/

/-- `c₁_w([y]) ∧ c₂_w(x, y)`: an indefinite `[y]` of kind `c₁` standing in the relation `c₂`
to the external variable `x` — `D ≡ DIORAMA([d]) ∧ MADE(x, d)` (112), `O ≡ CAR([c]) ∧
OWNS(x, c)` (137). -/
def indefOwned (c₁ : Lex 1) (c₂ : Lex 2) (y : Var) : Fm :=
  .conj (pred₁ c₁ (.bvar y)) (pred₂ c₂ (.var .x) (.var y))

variable (c₁ : Lex 1) (c₂ : Lex 2) {y : Var}

theorem locals_indefOwned : (indefOwned c₁ c₂ y).locals = [y] := rfl

theorem felicitous_indefOwned : (indefOwned c₁ c₂ y).Felicitous S.model h :=
  Expr.felicitous_of_presupFree _ _ (of_decide_eq_true rfl) _

-- (112)
theorem realize_sigma_indefOwned (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀})
    (hyw : y ≠ .w) (hyx : y ≠ .x) :
    Term.realize S.model h (.sigma y (indefOwned c₁ c₂ y)) =
      Sum.inr '' {e | S.rel c₁ w₀ ![e] ∧ S.rel c₂ w₀ ![x₀, e]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [locals_indefOwned]
  rcases a with _ | e <;> simp [indefOwned, realize_pred₁, realize_pred₂, hyw.symm, hyx.symm, hw,
    hx, world_inj]

theorem realize_sigmaW_indefOwned (hx : h .x = {Sum.inr x₀}) (hyw : y ≠ .w) (hyx : y ≠ .x) :
    Term.realize S.model h (.sigma .w (indefOwned c₁ c₂ y)) =
      Sum.inl '' {w | ∃ e, S.rel c₁ w ![e] ∧ S.rel c₂ w ![x₀, e]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [locals_indefOwned]
  rcases a with w | _ <;> simp [indefOwned, realize_pred₁, realize_pred₂, hyw, hyx.symm, hx,
    world]
  exact ⟨fun ⟨_, ⟨e, h₁, he⟩, _, he', h₂⟩ => ⟨e, h₁, Sum.inr_injective (he.trans he') ▸ h₂⟩,
    fun ⟨e, h₁, h₂⟩ => ⟨fun _ => .inr e, ⟨e, h₁, rfl⟩, e, rfl, h₂⟩⟩

theorem felicitous_sgPronoun_indefOwned_iff (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀})
    (hyw : y ≠ .w) (hyx : y ≠ .x) :
    (Term.sgPronoun y (indefOwned c₁ c₂ y)).Felicitous S.model h ↔
      ∃! e, S.rel c₁ w₀ ![e] ∧ S.rel c₂ w₀ ![x₀, e] := by
  rw [Term.felicitous_sgPronoun, realize_sigma_indefOwned S h c₁ c₂ hw hx hyw hyx,
    Sum.inr_injective.exists_image_eq_singleton_iff, Set.singleton_iff_unique_mem]
  exact and_iff_right (Term.felicitous_sigma_of_forall _ _ fun g => felicitous_indefOwned S g c₁ c₂)

/-- `O ≡ CAR_w([c]) ∧ OWNS_w(x, c)` (137). -/
def ownCar : Fm := indefOwned .car .owns .c

/-- `NOT^O`: `w ∉ ΣwO` (136)–(137), "he doesn't own a car". -/
def notOwn : Fm := .neg (.mem (.var .w) (.sigma .w (.label .O)))

/-- (139): "He doesn't own a car. #It is in the shop." -/
def shop139 : Fm :=
  .conj (.conj notOwn (pred₁ .inShop (Term.sgPronoun .c (.label .O)))) (.labelDef .O ownCar)

/-- (138b): "It's not like he doesn't own a car. It is just in the shop." -/
def shop138 : Fm :=
  .conj (.conj (.neg (.mem (.var .w) (.sigma .w notOwn)))
      (pred₁ .inShop (Term.sgPronoun .c (.label .O))))
    (.labelDef .O ownCar)

theorem expandSelf_shop139 :
    shop139.expandSelf =
      .conj (.conj (.neg (.mem (.var .w) (.sigma .w ownCar)))
          (pred₁ .inShop (Term.sgPronoun .c ownCar)))
        (.labelDef .O ownCar) := rfl

theorem expandSelf_shop138 :
    shop138.expandSelf =
      .conj (.conj (.neg (.mem (.var .w) (.sigma .w (.neg (.mem (.var .w) (.sigma .w ownCar))))))
          (pred₁ .inShop (Term.sgPronoun .c ownCar)))
        (.labelDef .O ownCar) := rfl

-- (139)
theorem felicitous_shop139_iff (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀}) :
    shop139.expandSelf.Felicitous S.model h ↔ ∃ c, S.rel .car w₀ ![c] ∧ S.rel .owns w₀ ![x₀, c] := by
  rw [expandSelf_shop139]
  simp only [Formula.felicitous_conj, Formula.felicitous_neg, Formula.felicitous_mem,
    Formula.felicitous_labelDef, Formula.realize_neg, Term.felicitous_var, ownCar,
    Term.felicitous_sigma_of_forall _ _ fun g => felicitous_indefOwned S g .car .owns,
    realize_mem_world S h hw, realize_sigmaW_indefOwned S h _ _ hx (show Var.c ≠ Var.w by decide)
      (show Var.c ≠ Var.x by decide), Set.mem_image, Set.mem_ofPred_eq, Sum.inl.injEq,
    exists_eq_right, felicitous_pred₁, felicitous_sgPronoun_indefOwned_iff S h _ _ hw hx
      (show Var.c ≠ Var.w by decide) (show Var.c ≠ Var.x by decide), implies_true, true_and,
    and_true]
  exact ⟨fun H => not_not.1 fun hn => hn (H hn).exists, fun H hn => absurd H hn⟩

-- (138b)
theorem not_realize_shop138 (hw : h .w = world w₀) (a₁ : Atom W E) (ha : a₁ ≠ Sum.inl w₀) :
    ¬ shop138.expandSelf.Realize S.model h := by
  rw [expandSelf_shop138]
  rintro ⟨⟨hneg, -⟩, -⟩
  refine hneg ((realize_mem_world S h hw _).2 ?_)
  rw [Term.mem_realize_sigma]
  refine ⟨Function.update h .w {Sum.inl w₀, a₁}, fun y hy => Function.update_of_ne hy.2 _ _,
    by simp, ?_⟩
  rintro ⟨a, hd, -⟩
  have hd' : ({Sum.inl w₀, a₁} : Set (Atom W E)) = {a} := hd
  exact ha ((Set.mem_singleton_iff.1 (hd' ▸ Set.mem_insert_of_mem _ (Set.mem_singleton a₁))).trans
    (Set.mem_singleton_iff.1 (hd' ▸ Set.mem_insert _ _)).symm)

/-- (139) is never both true and felicitous, as its `#` records: the first sentence denies the
car whose uniqueness the pronoun presupposes. -/
theorem judgment_139 (hw : h .w = world w₀) (hx : h .x = {Sum.inr x₀}) :
    shop139.expandSelf.Realize S.model h ∧ shop139.expandSelf.Felicitous S.model h ↔
      Examples.ex_139.judgment = .acceptable := by
  refine iff_of_false (fun ⟨hr, hf⟩ => ?_) (by decide)
  rw [felicitous_shop139_iff S h hw hx] at hf
  rw [expandSelf_shop139] at hr
  refine hr.1.1 ((realize_mem_world S h hw _).2 ?_)
  rw [ownCar, realize_sigmaW_indefOwned S h _ _ hx (show Var.c ≠ Var.w by decide)
    (show Var.c ≠ Var.x by decide)]
  exact ⟨w₀, hf, rfl⟩

/-- (138a) is acceptable, but its translation (138b) is false in every model with an entity:
`w ∉ ΣwO` is true of every plurality that is not a world, so `w` belongs to the summation over
it. -/
theorem judgment_138a (hw : h .w = world w₀) (e : E) :
    Examples.ex_138a.judgment = .acceptable ∧ ¬ shop138.expandSelf.Realize S.model h :=
  ⟨rfl, not_realize_shop138 S h hw (Sum.inr e) Sum.inr_ne_inl⟩

/-! ### Negation and disjunction -/

/-- `X ≡ SG(b) ∧ BATHROOM_w([b]) ∧ HERE_w(b)` (143). -/
def bathroomX : Fm := sgIndefWith .bathroom .here .b

/-- (143): "Either there is no bathroom here or it's in a funny place",
`(w ∉ ΣwX ∨ FUNNY-PLACE_w(ΣbX | SG(ΣbX))) ∧ X ≡ …`. -/
def bathroom143 : Fm :=
  .conj (Formula.disj (.neg (.mem (.var .w) (.sigma .w (.label .X))))
      (pred₁ .funnyPlace (Term.sgPronoun .b (.label .X))))
    (.labelDef .X bathroomX)

theorem felicitous_bathroomX : bathroomX.Felicitous S.model h :=
  felicitous_sgIndefWith S h _ _ _

theorem realize_sigmaB_bathroomX (hw : h .w = world w₀) :
    Term.realize S.model h (.sigma .b bathroomX) =
      Sum.inr '' {e | S.rel .bathroom w₀ ![e] ∧ S.rel .here w₀ ![e]} :=
  realize_sigma_sgIndefWith S h _ _ (by decide) hw

theorem realize_sigmaW_bathroomX :
    Term.realize S.model h (.sigma .w bathroomX) =
      Sum.inl '' {w | ∃ e, S.rel .bathroom w ![e] ∧ S.rel .here w ![e]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [bathroomX, locals_sgIndefWith]
  rcases a with w | _ <;> simp [sgIndefWith, sgIndef, realize_pred₁, world]
  exact ⟨fun ⟨_, ⟨e, h₁, he⟩, _, h₂, he'⟩ => ⟨e, h₁, Sum.inr_injective (he.trans he'.symm) ▸ h₂⟩,
    fun ⟨e, h₁, h₂⟩ => ⟨fun _ => .inr e, ⟨e, h₁, rfl⟩, e, h₂, rfl⟩⟩

theorem expandSelf_bathroom143 :
    bathroom143.expandSelf =
      .conj (Formula.disj (.neg (.mem (.var .w) (.sigma .w bathroomX)))
          (pred₁ .funnyPlace (Term.sgPronoun .b bathroomX)))
        (.labelDef .X bathroomX) := rfl

/-- (145): the bathroom disjunction is felicitous at `w₀` iff, if there is a bathroom here,
there is exactly one. -/
theorem felicitous_bathroom143_iff (hw : h .w = world w₀) :
    bathroom143.expandSelf.Felicitous S.model h ↔
      ((∃ e, S.rel .bathroom w₀ ![e] ∧ S.rel .here w₀ ![e]) →
        ∃! e, S.rel .bathroom w₀ ![e] ∧ S.rel .here w₀ ![e]) := by
  rw [expandSelf_bathroom143]
  simp only [Formula.felicitous_conj, Formula.felicitous_disj, Formula.felicitous_neg,
    Formula.felicitous_mem, Formula.felicitous_labelDef, Formula.realize_neg, not_not,
    Term.felicitous_var, Term.felicitous_sigma_of_forall _ _ (felicitous_bathroomX S),
    realize_mem_world S h hw, realize_sigmaW_bathroomX, Set.mem_image, Set.mem_ofPred_eq,
    Sum.inl.injEq, exists_eq_right, felicitous_pred₁, Term.felicitous_sgPronoun,
    realize_sigmaB_bathroomX S h hw, Sum.inr_injective.exists_image_eq_singleton_iff,
    Set.singleton_iff_unique_mem, implies_true, true_and, and_true]

/-! ### Donkey pronouns -/

theorem realize_sigma_pred₁ (c : Lex 1) {i : Var} (hi : i ≠ .w) (hw : h .w = world w₀) :
    Term.realize S.model h (.sigma i (pred₁ c (.bvar i))) = Sum.inr '' {e | S.rel c w₀ ![e]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [show (pred₁ c (.bvar i)).locals = [i] from rfl]
  rcases a with _ | e <;> simp [realize_pred₁, hi.symm, hw, world_inj]

/-- `V ≡ VALUABLES_w([v])` (116). -/
def valuableV : Fm := pred₁ .valuable (.bvar .v)

/-- `B ≡ V ∧ BROUGHT_w(x, v)` (116): the valuables that `x` brought. -/
def broughtB : Fm := indefOwned .valuable .bring .v

/-- The restriction `A ≡ ρ ∧ SOME(ΣvV, ΣvB)` of (116), for a description `ρ` of `x`. -/
def valuablesA (ρ : Fm) : Fm := .conj ρ (Formula.some (.sigma .v valuableV) (.sigma .v broughtB))

/-- The reference set `L ≡ A ∧ LOCKED_w(x, ΣvB)` of (116). -/
def valuablesL (ρ : Fm) : Fm := .conj (valuablesA ρ) (pred₂ .lock (.var .x) (.sigma .v broughtB))

/-- (116): "Everyone who brought something valuable locked it up", `EVERY(ΣxA, ΣxL)` with the
indefinite a quantifier `SOME(ΣvV, ΣvB)` and `it` the summation pronoun `ΣvB`, for a
description `ρ` of `x`: `PERSON_w([x])` as printed. -/
def valuables116 (ρ : Fm) : Fm :=
  .conj (.subset (.sigma .x (.label .A)) (.sigma .x (.label .L)))
    (.conj (.labelDef .V valuableV)
      (.conj (.labelDef .B (.conj (.label .V) (pred₂ .bring (.var .x) (.var .v))))
        (.conj (.labelDef .A (.conj ρ (Formula.some (.sigma .v (.label .V))
            (.sigma .v (.label .B)))))
          (.labelDef .L (.conj (.label .A) (pred₂ .lock (.var .x) (.sigma .v (.label .B))))))))

theorem expandSelf_valuables116_sgIndef :
    (valuables116 (sgIndef .person .x)).expandSelf =
      .conj (.subset (.sigma .x (valuablesA (sgIndef .person .x)))
          (.sigma .x (valuablesL (sgIndef .person .x))))
        (.conj (.labelDef .V valuableV) (.conj (.labelDef .B broughtB)
          (.conj (.labelDef .A (valuablesA (sgIndef .person .x)))
            (.labelDef .L (valuablesL (sgIndef .person .x)))))) := rfl

theorem expandSelf_valuables116_person :
    (valuables116 (pred₁ .person (.bvar .x))).expandSelf =
      .conj (.subset (.sigma .x (valuablesA (pred₁ .person (.bvar .x))))
          (.sigma .x (valuablesL (pred₁ .person (.bvar .x)))))
        (.conj (.labelDef .V valuableV) (.conj (.labelDef .B broughtB)
          (.conj (.labelDef .A (valuablesA (pred₁ .person (.bvar .x))))
            (.labelDef .L (valuablesL (pred₁ .person (.bvar .x))))))) := rfl

theorem realize_valuablesA_sgIndef (hw : h .w = world w₀) :
    (valuablesA (sgIndef .person .x)).Realize S.model h ↔ ∃ p, h .x = {Sum.inr p} ∧
      S.rel .person w₀ ![p] ∧ ∃ v, S.rel .valuable w₀ ![v] ∧ S.rel .bring w₀ ![p, v] := by
  rw [valuablesA, Formula.realize_conj, realize_sgIndef S h _ _ hw, Formula.realize_some,
    valuableV, realize_sigma_pred₁ S h _ (by decide) hw]
  constructor
  · rintro ⟨⟨p, hx, hp⟩, hs⟩
    rw [broughtB, realize_sigma_indefOwned S h _ _ hw hx (by decide) (by decide),
      ← Set.image_inter Sum.inr_injective, Set.image_nonempty] at hs
    obtain ⟨v, -, hv⟩ := hs
    exact ⟨p, hx, hp, v, hv⟩
  · rintro ⟨p, hx, hp, v, hv⟩
    rw [broughtB, realize_sigma_indefOwned S h _ _ hw hx (by decide) (by decide),
      ← Set.image_inter Sum.inr_injective, Set.image_nonempty]
    exact ⟨⟨p, hx, hp⟩, v, hv.1, hv⟩

theorem realize_valuablesL_sgIndef (hw : h .w = world w₀) :
    (valuablesL (sgIndef .person .x)).Realize S.model h ↔ ∃ p, h .x = {Sum.inr p} ∧
      S.rel .person w₀ ![p] ∧ (∃ v, S.rel .valuable w₀ ![v] ∧ S.rel .bring w₀ ![p, v]) ∧
        ∀ v, S.rel .valuable w₀ ![v] → S.rel .bring w₀ ![p, v] → S.rel .lock w₀ ![p, v] := by
  rw [valuablesL, Formula.realize_conj, realize_valuablesA_sgIndef S h hw, realize_pred₂, hw]
  simp only [world_inj, exists_eq_left', Term.realize_var]
  constructor
  · rintro ⟨⟨p, hx, hp, hv⟩, -, -, H⟩
    refine ⟨p, hx, hp, hv, fun v hv₁ hv₂ => ?_⟩
    rw [broughtB, realize_sigma_indefOwned S h _ _ hw hx (by decide) (by decide)] at H
    obtain ⟨_, _, h₁, h₂, hl⟩ := H _ (by rw [hx]; exact Set.mem_singleton _) _ ⟨v, ⟨hv₁, hv₂⟩, rfl⟩
    rwa [← Sum.inr_injective h₁, ← Sum.inr_injective h₂] at hl
  · rintro ⟨p, hx, hp, ⟨v, hv⟩, H⟩
    rw [broughtB, realize_sigma_indefOwned S h _ _ hw hx (by decide) (by decide), hx]
    refine ⟨⟨p, rfl, hp, v, hv⟩, Set.singleton_nonempty _, ⟨_, v, hv, rfl⟩, ?_⟩
    rintro _ rfl _ ⟨v', hv', rfl⟩
    exact ⟨p, v', rfl, rfl, H v' hv'.1 hv'.2⟩

/-- (116) with a singular restriction has the strong reading at `w₀`: everyone who brought
something valuable locked up every valuable they brought. -/
theorem realize_valuables116_sgIndef_iff (hw : h .w = world w₀) :
    (valuables116 (sgIndef .person .x)).expandSelf.Realize S.model h ↔
      ∀ p, S.rel .person w₀ ![p] → (∃ v, S.rel .valuable w₀ ![v] ∧ S.rel .bring w₀ ![p, v]) →
        ∀ v, S.rel .valuable w₀ ![v] → S.rel .bring w₀ ![p, v] → S.rel .lock w₀ ![p, v] := by
  have hl : ∀ {g : Var → Set (Atom W E)}, Set.EqOn g h
      {y | y ∉ (sgIndef .person .x).locals ∧ y ≠ .x} → g .w = world w₀ :=
    fun hg => (hg ⟨by decide, by decide⟩).trans hw
  rw [expandSelf_valuables116_sgIndef]
  simp only [Formula.realize_conj, Formula.realize_subset, Formula.realize_labelDef, and_true,
    Term.realize_sigma_eq_image S.model h (f := Sum.inr) fun g hg =>
      realize_valuablesA_sgIndef S g (hl hg),
    Term.realize_sigma_eq_image S.model h (f := Sum.inr) fun g hg =>
      realize_valuablesL_sgIndef S g (hl hg),
    Set.image_subset_image_iff Sum.inr_injective]
  exact ⟨fun H p hp hv => (@H p ⟨hp, hv⟩).2.2, fun H p ⟨hp, hv⟩ => ⟨hp, hv, H p hp hv⟩⟩

/-- The entities of a scenario for (116): two people and two valuables. -/
inductive Thing
  | a | b | v₁ | v₂
  deriving DecidableEq

/-- Both people brought the first valuable and locked it up; the first also brought the second
valuable and left it out. -/
def lockScenario : Scenario Unit Thing where
  acc _ _ := False
  most _ _ := False
  rel c _ es := match c with
    | .person => es 0 ∈ [Thing.a, .b]
    | .valuable => es 0 ∈ [Thing.v₁, .v₂]
    | .bring => (es 0, es 1) ∈ [(Thing.a, Thing.v₁), (.b, .v₁), (.a, .v₂)]
    | .lock => (es 0, es 1) ∈ [(Thing.a, Thing.v₁), (.b, .v₁)]
    | _ => False

-- (116)
theorem realize_valuables116_not_strong :
    (valuables116 (pred₁ .person (.bvar .x))).expandSelf.Realize lockScenario.model
        (fun _ => world ()) ∧
      lockScenario.rel .bring () ![.a, .v₂] ∧ ¬ lockScenario.rel .lock () ![.a, .v₂] := by
  refine ⟨?_, by simp [lockScenario], by simp [lockScenario]⟩
  have hB : ∀ g : Var → Set (Atom Unit Thing), g .w = world () → g .x = {.inr .a, .inr .b} →
      Term.realize lockScenario.model g (.sigma .v broughtB) = {.inr .v₁} := fun g hw hx => by
    rw [Term.realize_sigma_eq_of_isConjunctive _ _ lockScenario.divisive rfl]
    ext a
    simp only [broughtB, locals_indefOwned]
    rcases a with _ | e
    · simp [indefOwned, realize_pred₁]
    · cases e <;> simp [indefOwned, realize_pred₁, realize_pred₂, hw, hx, lockScenario, world]
  rw [expandSelf_valuables116_person]
  simp only [Formula.realize_conj, Formula.realize_subset, Formula.realize_labelDef, and_true]
  intro _ ha
  rw [Term.mem_realize_sigma] at ha
  obtain ⟨g, -, ha, hA⟩ := ha
  rw [valuablesA, Formula.realize_conj, realize_pred₁, Term.realize_bvar] at hA
  obtain ⟨⟨_, -, -, hs⟩, -⟩ := hA
  obtain ⟨p, hp, rfl⟩ := hs ha
  let G := Function.update (fun _ => world ()) Var.x {.inr Thing.a, .inr Thing.b}
  have hGx : G .x = {.inr .a, .inr .b} := Function.update_self ..
  have hGw : G .w = world () := Function.update_of_ne (by decide) ..
  rw [Term.mem_realize_sigma]
  refine ⟨G, fun y hy => Function.update_of_ne hy.2 _ _, ?_, ?_⟩
  · rw [hGx]
    cases p <;> simp_all [lockScenario]
  rw [valuablesL, valuablesA, Formula.realize_conj, Formula.realize_conj, realize_pred₁,
    Formula.realize_some, valuableV, realize_sigma_pred₁ _ G .valuable (i := .v) (by decide) hGw,
    realize_pred₂, hB G hGw hGx]
  simp only [Term.realize_bvar, Term.realize_var, hGx, hGw, true_and]
  refine ⟨⟨⟨(), Set.insert_nonempty _ _, Set.insert_subset_iff.2 ⟨⟨.a, by simp [lockScenario], rfl⟩,
    Set.singleton_subset_iff.2 ⟨.b, by simp [lockScenario], rfl⟩⟩⟩,
    ⟨.inr .v₁, ⟨.v₁, by simp [lockScenario], rfl⟩, rfl⟩⟩, (), Set.insert_nonempty _ _,
    Set.singleton_nonempty _, ?_⟩
  rintro _ (rfl | rfl) _ rfl <;> exact ⟨_, _, rfl, rfl, by simp [lockScenario]⟩

/-! ### Presupposition under quantification -/

/-- `K ≡ MONARCH-OF_w([k], m)`; `ΣkK | SG(ΣkK)` is "its monarch". -/
def monarchK : Fm := pred₂ .monarchOf (.bvar .k) (.var .m)

/-- `Z ∧ CHERISH_w(m, ΣkK | SG(ΣkK))`: the nuclear scope of "cherishes its monarch" over the
restriction `Z`, the pronoun's presupposition to be satisfied by `Z`. -/
def cherishBody (Z : Lab) : Fm :=
  .conj (.label Z) (pred₂ .cherish (.var .m) (Term.sgPronoun .k (.label .K)))

/-- `C ≡ SG(m) ∧ COUNTRY_w([m])`. -/
def countryC : Fm := sgIndef .country .m

/-- `M ≡ C ∧ MONARCHY_w(m)`: the reference set of "every European country was a monarchy". -/
def monarchyM : Fm := .conj (.label .C) (pred₁ .monarchy (.var .m))

/-- (150a): "Every European country was a monarchy. Most of them cherished their monarchs.",
in our translation the subordinate quantifier's restriction the first sentence's reference-set
label `M`; the paper prints none. -/
def discourse150a : Fm :=
  .conj (.conj (.subset (.sigma .m (.label .C)) (.sigma .m (.label .M)))
      (.atom .most (.var .w) ![.sigma .m (.label .M), .sigma .m (.label .S)]))
    (.conj (.labelDef .C countryC) (.conj (.labelDef .M monarchyM)
      (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody .M)))))

/-- The nuclear scope with the restriction and the pronoun's label expanded. -/
def cherishBody' (ρ : Fm) : Fm :=
  .conj ρ (pred₂ .cherish (.var .m) (Term.sgPronoun .k monarchK))

/-- `M` with `C` expanded. -/
def monarchyM' : Fm := sgIndefWith .country .monarchy .m

theorem expandSelf_discourse150a :
    discourse150a.expandSelf =
      .conj (.conj (.subset (.sigma .m countryC) (.sigma .m monarchyM'))
          (.atom .most (.var .w) ![.sigma .m monarchyM', .sigma .m (cherishBody' monarchyM')]))
        (.conj (.labelDef .C countryC) (.conj (.labelDef .M monarchyM')
          (.conj (.labelDef .K monarchK) (.labelDef .S (cherishBody' monarchyM'))))) := rfl

theorem felicitous_monarchK : monarchK.Felicitous S.model h :=
  Expr.felicitous_of_presupFree _ _ (by decide) _

theorem realize_sigmaK_monarchK {m₀ : E} (hw : h .w = world w₀) (hm : h .m = {Sum.inr m₀}) :
    Term.realize S.model h (.sigma .k monarchK) = Sum.inr '' {e | S.rel .monarchOf w₀ ![e, m₀]} := by
  rw [Term.realize_sigma_eq_of_isConjunctive _ _ S.divisive rfl]
  ext a
  have : Nonempty (Atom W E) := ⟨a⟩
  simp only [show monarchK.locals = [.k] from rfl]
  rcases a with _ | e <;> simp [monarchK, realize_pred₂, hw, hm, world_inj]

theorem felicitous_sgPronoun_monarchK_iff {m₀ : E} (hw : h .w = world w₀)
    (hm : h .m = {Sum.inr m₀}) :
    (Term.sgPronoun .k monarchK).Felicitous S.model h ↔ ∃! e, S.rel .monarchOf w₀ ![e, m₀] := by
  rw [Term.felicitous_sgPronoun, realize_sigmaK_monarchK S h hw hm,
    Sum.inr_injective.exists_image_eq_singleton_iff, Set.singleton_iff_unique_mem]
  exact and_iff_right (Term.felicitous_sigma_of_forall _ _ (felicitous_monarchK S))

theorem felicitous_sigmaM_cherishBody'_iff {ρ : Fm} {Q : E → Prop} (hw : h .w = world w₀)
    (hlw : Var.w ∉ ρ.locals) (hρf : ∀ g, ρ.Felicitous S.model g)
    (hρ : ∀ g : Var → Set (Atom W E), g .w = world w₀ →
      (ρ.Realize S.model g ↔ ∃ m₀, g .m = {Sum.inr m₀} ∧ Q m₀)) :
    (Expr.sigma .m (cherishBody' ρ)).Felicitous S.model h ↔
      ∀ m₀, Q m₀ → ∃! e, S.rel .monarchOf w₀ ![e, m₀] := by
  rw [Term.felicitous_sigma]
  constructor
  · intro H m₀ hm
    have hg : Set.EqOn (Function.update h .m {Sum.inr m₀}) h
        {y | y ∉ (cherishBody' ρ).locals ∧ y ≠ Var.m} := fun y hy => Function.update_of_ne hy.2 _ _
    have hw' : Function.update h .m {Sum.inr m₀} .w = world w₀ := by
      rw [Function.update_of_ne (by decide), hw]
    obtain ⟨-, H'⟩ := H _ hg
    exact (felicitous_sgPronoun_monarchK_iff S _ hw' (Function.update_self ..)).1
      ((felicitous_pred₂ S _ _ _ _).1 (H' ((hρ _ hw').2 ⟨m₀, Function.update_self .., hm⟩))).2
  · intro H g' hg
    have hl : (cherishBody' ρ).locals = ρ.locals := by
      show ρ.locals ++ (pred₂ .cherish (.var .m) (Term.sgPronoun .k monarchK)).locals = ρ.locals
      rw [show (pred₂ .cherish (.var .m) (Term.sgPronoun .k monarchK)).locals = [] from rfl,
        List.append_nil]
    have hw' : g' .w = world w₀ := by rw [hg ⟨by rw [hl]; exact hlw, by decide⟩, hw]
    refine ⟨hρf g', fun hr => (felicitous_pred₂ S _ _ _ _).2 ⟨trivial, ?_⟩⟩
    obtain ⟨m₀, hm, hq⟩ := (hρ g' hw').1 hr
    exact (felicitous_sgPronoun_monarchK_iff S g' hw' hm).2 (H m₀ hq)

/-- (150a) is felicitous at `w₀` iff, granted its first sentence, every country that is a monarchy
has exactly one monarch. -/
theorem felicitous_discourse150a_iff (hw : h .w = world w₀) :
    discourse150a.expandSelf.Felicitous S.model h ↔
      ((∀ e, S.rel .country w₀ ![e] → S.rel .monarchy w₀ ![e]) →
        ∀ m₀, S.rel .country w₀ ![m₀] ∧ S.rel .monarchy w₀ ![m₀] →
          ∃! e, S.rel .monarchOf w₀ ![e, m₀]) := by
  rw [expandSelf_discourse150a]
  simp only [Formula.felicitous_conj, Formula.felicitous_subset, Formula.felicitous_atom,
    Formula.felicitous_labelDef, Formula.realize_labelDef, Formula.realize_subset,
    Term.felicitous_var, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, countryC,
    monarchyM', Term.felicitous_sigma_of_forall _ _ fun g => felicitous_sgIndef S g _ _,
    Term.felicitous_sigma_of_forall _ _ fun g => felicitous_sgIndefWith S g _ _ _, implies_true,
    and_true, true_and, realize_sigma_sgIndef S h .country (i := .m) (by decide) hw,
    realize_sigma_sgIndefWith S h .country .monarchy (i := .m) (by decide) hw,
    Set.image_subset_image_iff Sum.inr_injective, Set.ofPred_subset_ofPred,
    felicitous_sigmaM_cherishBody'_iff S h hw (by decide)
      (fun g => felicitous_sgIndefWith S g _ _ _)
      (fun g hg => realize_sgIndefWith S g .country .monarchy .m hg)]
  exact imp_congr_left ⟨fun H e he => (H e he).2, fun H e he => ⟨he, H e he⟩⟩

/-! ### Discourse translation -/

/-- (150a) has a translation ((31a)): `S` is defined through `M` and `K`, `M` through `C`. -/
example : discourse150a.HasDiscourseTranslation := by
  have hdefs : discourse150a.defs =
      [(.C, countryC), (.M, monarchyM), (.K, monarchK), (.S, cherishBody .M)] := rfl
  let rank : Lab → ℕ := fun Z => if Z = .S then 2 else if Z = .M then 1 else 0
  have hrank : ∀ {Z Z'}, DependsOn discourse150a.defs Z Z' → rank Z' < rank Z := by
    rintro Z Z' ⟨ψ, h, hZ'⟩
    rw [hdefs] at h
    cases Z <;> simp [List.lookup_cons, beq_eq_decide] at h <;> subst h <;>
      simp_all [rank, countryC, monarchyM, monarchK, cherishBody, sgIndef, pred₁, pred₂,
        Term.sgPronoun, Expr.labels, Fin.exists_fin_two]
    rcases hZ' with rfl | rfl <;> decide
  refine ⟨fun Z ψ ψ' h h' => (Prod.mk.inj (List.inj_on_of_nodup_map (f := Prod.fst)
    (by rw [hdefs]; decide) h h' rfl)).2, fun Z hZ => ?_, fun Z hZ => ?_⟩
  · have : ∀ {Z Z'}, Relation.TransGen (DependsOn discourse150a.defs) Z Z' → rank Z' < rank Z := by
      intro Z Z' h
      induction h with
      | single h => exact hrank h
      | tail _ h ih => exact (hrank h).trans ih
    exact lt_irrefl _ (this hZ)
  · have : Z = .C ∨ Z = .M ∨ Z = .K ∨ Z = .S := by
      simp [discourse150a, countryC, monarchyM, monarchK, cherishBody, sgIndef, pred₁, pred₂,
        Term.sgPronoun, Expr.labels, Fin.exists_fin_two] at hZ
      tauto
    rw [hdefs]
    rcases this with rfl | rfl | rfl | rfl <;> simp [List.lookup_cons, beq_eq_decide]

/-- A circular definition is never expanded away: `X ∧ X ≡ X` has no translation, and keeps its
defined label `X` ((30)). -/
example : ¬ Formula.HasDiscourseTranslation (.conj (.label .X) (.labelDef .X (.label .X)) : Fm) ∧
    Lab.X ∈ (Formula.expandSelf (.conj (.label .X) (.labelDef .X (.label .X))) : Fm).labels ∧
    (Expr.defs (.conj (.label .X) (.labelDef .X (.label .X)) : Fm)).lookup .X ≠ none :=
  ⟨fun h => h.not_circular .X (.single ⟨_, rfl, rfl⟩), by
    simp [Formula.expandSelf, Formula.expand, Expr.defs, Expr.substLabels, Expr.labels]⟩

end AbneyKeshet2025
