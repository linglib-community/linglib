module

public import Linglib.Semantics.Composition.Tree

/-!
# Translation into typed λ-terms

Montague interprets a sentence indirectly, by translating it into a logical language and
interpreting the translation; Heim and Kratzer interpret trees directly. The two agree. The
logical language is the simply typed λ-calculus over a signature of constants (`Montague.Term`),
with variables of type `e`, abstraction over them, and term formers for the rigid intension of a
term, predicate modification and event identification, the operations of the composition modes
other than application. A term denotes under an interpretation of the constants and an
assignment of the variables (`Montague.Term.eval`).

The composition modes compose terms as they compose denotations (`HeimKratzer.Tree.Modes.term`),
so a tree translates to a term, its logical form (`HeimKratzer.Tree.translate`): a trace
translates to the variable of its index and a binder to the abstraction over it. Evaluation
commutes with the modes (`Montague.Term.isHom_eval`), and so the denotation `Tree.interp`
computes is the evaluation of the translation whenever the words translate to closed terms
(`HeimKratzer.Tree.interp_eq_map_translate`).

## Main definitions

* `Montague.Term`: the typed λ-terms over a signature.
* `Montague.Term.eval`: the denotation of a term.
* `HeimKratzer.Tree.Modes.term`: the composition modes on terms.
* `HeimKratzer.Tree.translate`: the term a tree translates to.

## Main results

* `Montague.Term.eval_congr_of_agree`: a term's denotation depends on the assignment only at its
  free variables.
* `HeimKratzer.Tree.interp_eq_map_translate`: interpretation is evaluation of the translation.

## Implementation notes

Variables are named by the trace indices, so a binder with index `n` translates to `λn`, and the
translation needs no fresh names. Predicate modification and event identification are term
formers rather than abstractions over a fresh variable for the same reason. Evaluation is
noncomputable, a term of type `t` denoting a proposition; translation is computable, so the
logical form of a tree is computed.

## References

* [montague-1973]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Montague

/-- The typed λ-terms over a signature `K` of constants, by type: constants, the variables of type
`e`, application, abstraction over a variable of type `e`, the rigid intension of a term, and the
predicate modification and event identification of predicates. -/
inductive Term (K : Ty → Type) : Ty → Type where
  | const {ty : Ty} (c : K ty) : Term K ty
  | var (n : ℕ) : Term K .e
  | app {σ τ : Ty} (f : Term K (σ ⇒ τ)) (a : Term K σ) : Term K τ
  | lam {τ : Ty} (n : ℕ) (body : Term K τ) : Term K (.e ⇒ τ)
  | rigid {σ : Ty} (a : Term K σ) : Term K (.intens σ)
  | inter (p q : Term K (.e ⇒ .t)) : Term K (.e ⇒ .t)
  | evId (f : Term K (.e ⇒ .e ⇒ .t)) (p : Term K (.e ⇒ .t)) : Term K (.e ⇒ .e ⇒ .t)

namespace Term

variable {K : Ty → Type} {E W D : Type}

open scoped Assignment

/-- The free variables of a term. -/
def freeVars : {ty : Ty} → Term K ty → Finset ℕ
  | _, const _ => ∅
  | _, var n => {n}
  | _, app f a => f.freeVars ∪ a.freeVars
  | _, lam n b => b.freeVars.erase n
  | _, rigid a => a.freeVars
  | _, inter p q => p.freeVars ∪ q.freeVars
  | _, evId f p => f.freeVars ∪ p.freeVars

/-- A term is closed when it has no free variables. -/
def Closed {ty : Ty} (t : Term K ty) : Prop := t.freeVars = ∅

variable (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D)

/-- The denotation of a term under an interpretation of the constants and an assignment of the
variables. -/
noncomputable def eval (g : Assignment E) : {ty : Ty} → Term K ty → Ty.Domain E W ty D
  | _, const c => I c
  | _, var n => g n
  | _, app f a => eval g f (eval g a)
  | _, lam n b => fun x ↦ eval (g[n ↦ x]) b
  | _, rigid a => fun _ ↦ eval g a
  | _, inter p q => Modifier.intersective (eval g p) (eval g q)
  | _, evId f p => ArgumentStructure.eventIdentification (eval g f) (eval g p)

variable {I}

/-- A term's denotation depends on the assignment only at its free variables. -/
theorem eval_congr_of_agree {ty : Ty} (t : Term K ty) {g g' : Assignment E}
    (h : ∀ n ∈ t.freeVars, g n = g' n) : t.eval I g = t.eval I g' := by
  induction t generalizing g g' with
  | const c => rfl
  | var n => exact h n (Finset.mem_singleton_self n)
  | app f a ihf iha =>
    simp only [freeVars, Finset.mem_union] at h
    simp only [eval, ihf fun n hn ↦ h n (.inl hn), iha fun n hn ↦ h n (.inr hn)]
  | lam n b ih =>
    funext x
    refine ih fun m hm ↦ ?_
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [Function.update_of_ne hmn, h m (Finset.mem_erase.2 ⟨hmn, hm⟩)]
  | rigid a ih => funext _; exact ih h
  | inter p q ihp ihq =>
    simp only [freeVars, Finset.mem_union] at h
    simp only [eval, ihp fun n hn ↦ h n (.inl hn), ihq fun n hn ↦ h n (.inr hn)]
  | evId f p ihf ihp =>
    simp only [freeVars, Finset.mem_union] at h
    simp only [eval, ihf fun n hn ↦ h n (.inl hn), ihp fun n hn ↦ h n (.inr hn)]

/-- A closed term denotes alike under every assignment. -/
theorem Closed.eval_eq {ty : Ty} {t : Term K ty} (ht : t.Closed) (g g' : Assignment E) :
    t.eval I g = t.eval I g' :=
  t.eval_congr_of_agree fun n hn ↦ absurd (ht ▸ hn) (Finset.notMem_empty n)

end Term

end Montague

namespace HeimKratzer.Tree

open Montague

/-- The modes on terms build the term, the rigid intension of an argument where the function
expects an intension. -/
def Modes.term (K : Ty → Type) : Modes (Term K) where
  app := .app
  appRev a f := .app f a
  appRigid f a := .app f (.rigid a)
  appRigidRev a f := .app f (.rigid a)
  inter := .inter
  evId := .evId
  evIdRev p f := .evId f p

/-- Evaluation commutes with the modes. -/
theorem _root_.Montague.Term.isHom_eval {K : Ty → Type} {E W D : Type}
    (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D) (g : Assignment E) :
    (Modes.term K).IsHom (Modes.ofApplicative E W Id D) (Term.eval I g) where
  app _ _ := rfl
  appRev _ _ := rfl
  appRigid _ _ := rfl
  appRigidRev _ _ := rfl
  inter _ _ := rfl
  evId _ _ := rfl
  evIdRev _ _ := rfl

open PhraseStructure

section Translate

variable {C : Type} {K : Ty → Type} {L : Type*}

/-- The term a tree translates to, by the composition principles of [heim-kratzer-1998]: a
terminal translates to its leaf's term, a binary node to what the modes compose from its
daughters' terms, a trace to the variable of its index, and a binder to the abstraction over the
variable of its index. -/
def translate (lex : L → Option (Σ ty, Term K ty)) : Tree C L → Option (Σ ty, Term K ty)
  | .terminal _ w => lex w
  | .node _ (t :: []) => translate lex t
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← translate lex t1
    let d2 ← translate lex t2
    (Modes.term K).interpBinary d1 d2
  | .node _ _ => none
  | .adjoin _ (t :: []) => translate lex t
  | .adjoin _ (t1 :: t2 :: []) => do
    let d1 ← translate lex t1
    let d2 ← translate lex t2
    (Modes.term K).interpBinary d1 d2
  | .adjoin _ _ => none
  | .trace n _ => some ⟨.e, .var n⟩
  | .bind n _ body => (translate lex body).map fun d ↦ ⟨.e ⇒ d.1, .lam n d.2⟩
  | _ => none

variable (lex : L → Option (Σ ty, Term K ty))

@[simp] theorem translate_terminal (c : C) (w : L) :
    translate lex (.terminal c w : Tree C L) = lex w := rfl

@[simp] theorem translate_node_unary (c : C) (t : Tree C L) :
    translate lex (.node c (t :: [])) = translate lex t := rfl

@[simp] theorem translate_node_binary (c : C) (t₁ t₂ : Tree C L) :
    translate lex (.node c (t₁ :: t₂ :: [])) = ((translate lex t₁).bind fun d₁ ↦
      (translate lex t₂).bind fun d₂ ↦ (Modes.term K).interpBinary d₁ d₂) := rfl

@[simp] theorem translate_adjoin_unary (c : C) (t : Tree C L) :
    translate lex (.adjoin c (t :: [])) = translate lex t := rfl

@[simp] theorem translate_adjoin_binary (c : C) (t₁ t₂ : Tree C L) :
    translate lex (.adjoin c (t₁ :: t₂ :: [])) = ((translate lex t₁).bind fun d₁ ↦
      (translate lex t₂).bind fun d₂ ↦ (Modes.term K).interpBinary d₁ d₂) := rfl

@[simp] theorem translate_trace (n : ℕ) (c : C) :
    translate lex (.trace n c : Tree C L) = some ⟨.e, .var n⟩ := rfl

@[simp] theorem translate_bind (n : ℕ) (c : C) (body : Tree C L) :
    translate lex (.bind n c body) =
      (translate lex body).map fun d ↦ ⟨.e ⇒ d.1, .lam n d.2⟩ := rfl

/-- A node whose daughters its label does not license translates to nothing. -/
theorem translate_junk {l : Tree.Label C L} {cs : List (Tree C L)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    translate lex (RoseTree.node l cs) = none := by
  cases l with
  | terminal c w => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | node c => exact absurd trivial h
  | segment c => exact absurd trivial h
  | trace n c => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | bind n c =>
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩
    · rfl
    · exact absurd rfl h
    · rfl

end Translate

/-! ### Interpretation is evaluation of the translation -/

section Factorization

variable {C : Type} {K : Ty → Type} {L : Type*} {E W D : Type}
  (I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty D) {lex : L → Option (Σ ty, Term K ty)}

open scoped Assignment

/-- The denotation of a term under an assignment, at its type. -/
noncomputable abbrev evalValue (g : Assignment E) (d : Σ ty, Term K ty) : Denotation E W Id D :=
  ⟨d.1, d.2.eval I g⟩

/-- Interpretation is evaluation of the translation: where every word translates to a closed
term, interpreting a tree with each word denoting its term's denotation gives what the tree's
translation denotes, under every assignment. -/
theorem interp_eq_map_translate (hlex : ∀ w d, lex w = some d → d.2.Closed)
    (g₀ g : Assignment E) (t : Tree C L) :
    interp (fun w ↦ (lex w).map (evalValue I g₀)) g t = (translate lex t).map (evalValue I g) := by
  induction t using Tree.rec' generalizing g with
  | terminal c w =>
    simp only [interp_terminal, translate_terminal]
    cases h : lex w with
    | none => rfl
    | some d => simp [evalValue, (hlex w d h).eval_eq g₀ g]
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      rw [interp_node_binary, ih t₁ (by simp) g, ih t₂ (by simp) g, translate_node_binary]
      cases translate lex t₁ <;> cases translate lex t₂ <;> try rfl
      exact (Modes.interpBinary_map (Term.isHom_eval I g) _ _).symm
    | _ :: _ :: _ :: _ => rfl
  | adjoin c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      rw [interp_adjoin_binary, ih t₁ (by simp) g, ih t₂ (by simp) g, translate_adjoin_binary]
      cases translate lex t₁ <;> cases translate lex t₂ <;> try rfl
      exact (Modes.interpBinary_map (Term.isHom_eval I g) _ _).symm
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    rw [interp_bind, PredAbs.dist?_id, ih g, translate_bind]
    cases hb : translate lex body with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some, evalValue]
      congr 2
      funext x
      rw [ih (g[n ↦ x]), hb]
      simp [evalValue, Term.eval]
  | junk l cs hj _ => rw [interp_junk _ g hj, translate_junk lex hj]; rfl

end Factorization

end HeimKratzer.Tree
