module

public import Linglib.Semantics.Dynamic.Partial

/-!
# Formulas of the propositional fragment

This file defines the formulas on which theories of presupposition projection are compared, the
propositional fragment of the language L of Schlenker's Appendix C, which is also the language of
Kalomoiros's System 1 (Definition 3.4.1). A formula is built from atoms and triggers by negation and
the binary connectives of `Connective`; a trigger `trigger p p'` presupposes `p` and asserts `p'`,
and its classical meaning is the conjunction of the two (`Formula.truth`, C.2).

Each binary connective is interpreted classically (`Connective.eval`), by the truth table of any
trivalent connectives (`Connective.table`), and by Heim's context change potentials, with Beaver's
disjunction (`Connective.ccp`). The fold `Formula.eval` evaluates a formula into a trivalent
proposition `W → SignType` under given connectives, the Strong Kleene ones for
`Formula.strongKleene` and Peters' filtering ones for `Formula.middleKleene`, and `Formula.ccp`
evaluates it into `CCP.Partial`, sending an atom or a trigger to the update of its trivalent
meaning. Where the filtering evaluation is defined it is the classical meaning
(`Formula.middleKleene_eq_ofProp`). The context change potential admits a context iff the filtering
evaluation is defined throughout it, and it updates the context to its worlds at which the formula
is classically true (`Formula.admits_ccp_iff`, `Formula.ccp_get`).

A formula is written as a string of tokens (`Formula.yield`), with brackets, the dot after a
conditional's antecedent and a trigger as one token, as in Kalomoiros's Definition 3.4.1. The
string can be parsed back (`Formula.parse_yield`), so it determines the formula even when more
tokens follow (`Formula.yield_append_inj`): the strings are uniquely readable.

## Main definitions

* `Presupposition.Formula`: atoms, triggers, negation and the binary connectives.
* `Presupposition.Formula.truth`: the classical meaning at an interpretation of the atoms.
* `Presupposition.Formula.eval`: the evaluation under trivalent connectives, with
  `Presupposition.Formula.strongKleene` and `Presupposition.Formula.middleKleene` its Strong Kleene
  and filtering instances.
* `Presupposition.Formula.ccp`: the dynamic evaluation.
* `Presupposition.Formula.accommodate`: local accommodation, which keeps the classical meaning.
* `Presupposition.Token`, `Presupposition.Formula.yield`: the tokens and the string of a formula.
* `Presupposition.Formula.parse`: the parser, in the state monad of the remaining tokens.

## Implementation notes

The interpretation of the atoms is a function to `Set W`, and a trigger's trivalent meaning is the
conditional event of its assertion on its presupposition. Schlenker's Expressivity (C.3), that every
proposition is denoted by an atom, is not built in: the theories that need it quantify over
propositions where the paper quantifies over expressions. The conditional is material, as in the
paper, and its Strong Kleene clause is by interdefinability from negation and disjunction.

## References

* [schlenker-2009]
* [kalomoiros-2023]
* [karttunen-1974-presupposition]
* [peters-1979]
* [heim-1983]
* [beaver-2001]
-/

@[expose] public section

namespace Presupposition

open DynamicSemantics

variable {Atom W : Type*}

/-! ### Connectives -/

namespace Connective

/-- The classical truth function of a binary connective. -/
def eval : Connective → Prop → Prop → Prop
  | conj, a, b => a ∧ b
  | cond, a, b => a → b
  | disj, a, b => a ∨ b

/-- The truth table that the trivalent connectives `C` give a binary connective. -/
@[simp] def table (C : Trivalent.Connectives) : Connective → SignType → SignType → SignType
  | conj => C.conj
  | cond => C.cond
  | disj => C.disj

/-- The dynamic connectives are [heim-1983]'s conjunction and conditional and [beaver-2001]'s
disjunction. -/
noncomputable def ccp : Connective → CCP.Partial W → CCP.Partial W → CCP.Partial W
  | .conj => PartialUpdate.seq
  | .cond => CCP.Partial.cond
  | .disj => CCP.Partial.disj

end Connective

/-! ### Formulas -/

/-- The propositional fragment of L (C.1), in which a trigger `trigger p p'` presupposes `p` and
asserts `p'`. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  | trigger (presup assert : Atom)
  | not (F : Formula Atom)
  | bin (c : Connective) (F G : Formula Atom)
  deriving DecidableEq

namespace Formula

open Classical

variable (I : Atom → Set W)

/-- The classical meaning (C.2) reads a trigger as the conjunction of its two parts. -/
def truth : Formula Atom → Set W
  | atom p => I p
  | trigger p p' => I p ∩ I p'
  | not F => (truth F)ᶜ
  | bin c F G => {w | c.eval (w ∈ truth F) (w ∈ truth G)}

/-- The evaluation by the trivalent connectives `C`, in which an atom is classical and a trigger is
defined where its presupposition holds. -/
noncomputable def eval (C : Trivalent.Connectives) : Formula Atom → W → SignType
  | atom p => fun w ↦ SignType.ofProp (w ∈ I p)
  | trigger p p' => (I p).indicator fun w ↦ SignType.ofProp (w ∈ I p')
  | not F => -eval C F
  | bin c F G => fun w ↦ c.table C (eval C F w) (eval C G w)

/-- The Strong Kleene evaluation. -/
noncomputable abbrev strongKleene : Formula Atom → W → SignType := eval I .strongKleene

/-- The evaluation by [peters-1979]'s filtering connectives, the Middle Kleene tables. -/
noncomputable abbrev middleKleene : Formula Atom → W → SignType := eval I .middleKleene

/-- The context change potential of a formula updates an atom or a trigger by its trivalent
meaning, so a trigger is defined in a context that entails its presupposition. -/
noncomputable def ccp : Formula Atom → CCP.Partial W
  | atom p => CCP.Partial.ofTrivalent ((atom p).middleKleene I)
  | trigger p p' => CCP.Partial.ofTrivalent ((trigger p p').middleKleene I)
  | not F => CCP.Partial.neg (ccp F)
  | bin c F G => c.ccp (ccp F) (ccp G)

/-- [heim-1983]'s local accommodation: the presupposition of each trigger joins its assertion where
the trigger is. -/
def accommodate : Formula Atom → Formula Atom
  | atom p => atom p
  | trigger p p' => bin .conj (atom p) (atom p')
  | not F => not (accommodate F)
  | bin c F G => bin c (accommodate F) (accommodate G)

/-- Local accommodation keeps the classical meaning. -/
@[simp] theorem truth_accommodate (F : Formula Atom) : F.accommodate.truth I = F.truth I := by
  induction F with
  | atom => rfl
  | trigger => rfl
  | not F ih => simp [accommodate, truth, ih]
  | bin c F G ihF ihG => simp [accommodate, truth, ihF, ihG]

variable {w : W}

/-- The filtering evaluation of a binary formula is defined where the first argument's is, and
the second's wherever the world is in the second argument's local context
([karttunen-1974-presupposition]). -/
theorem middleKleene_bin_ne_zero_iff {c : Connective} {F G : Formula Atom}
    (hF : F.middleKleene I w ≠ 0 → F.middleKleene I w = SignType.ofProp (w ∈ F.truth I)) :
    (bin c F G).middleKleene I w ≠ 0 ↔
      F.middleKleene I w ≠ 0 ∧
        (w ∈ c.localContext Set.univ (F.truth I) → G.middleKleene I w ≠ 0) := by
  simp only [middleKleene, eval] at hF ⊢
  refine ⟨fun h ↦ ?_, fun ⟨h, hG⟩ ↦ ?_⟩
  · have h' : F.middleKleene I w ≠ 0 := by cases c <;> simp_all
    rw [hF h'] at h
    exact ⟨h', fun hl ↦ by cases c <;> simp_all [Connective.localContext]⟩
  · rw [hF h]
    cases c <;> by_cases ht : w ∈ F.truth I <;>
      simp_all [Connective.localContext]

/-- Where the filtering evaluation is defined, it is the classical meaning. -/
theorem middleKleene_eq_ofProp {F : Formula Atom} (h : F.middleKleene I w ≠ 0) :
    F.middleKleene I w = SignType.ofProp (w ∈ F.truth I) := by
  induction F with
  | atom p => rfl
  | trigger p p' =>
    by_cases hp : w ∈ I p <;> simp_all [middleKleene, eval, truth]
  | not F ih =>
    simp only [middleKleene, eval, Pi.neg_apply, ne_eq, SignType.neg_eq_zero_iff] at h ⊢
    simp [ih h, truth]
  | bin c F G ihF ihG =>
    obtain ⟨hF, hG⟩ := (middleKleene_bin_ne_zero_iff I ihF).1 h
    simp only [middleKleene, eval, ihF hF]
    cases c <;> by_cases ht : w ∈ F.truth I <;>
      simp_all [Connective.localContext, truth, Connective.eval]

/-- The filtering evaluation of a binary formula is defined where the first argument's is, and
the second's wherever the world is in the second argument's local context. -/
theorem middleKleene_bin_ne_zero {c : Connective} {F G : Formula Atom} :
    (bin c F G).middleKleene I w ≠ 0 ↔
      F.middleKleene I w ≠ 0 ∧ (w ∈ c.localContext Set.univ (F.truth I) → G.middleKleene I w ≠ 0) :=
  middleKleene_bin_ne_zero_iff I (middleKleene_eq_ofProp I)

/-- Every formula contains an atom or a trigger. -/
theorem nonempty_atom : Formula Atom → Nonempty Atom
  | atom p => ⟨p⟩
  | trigger p _ => ⟨p⟩
  | not F => nonempty_atom F
  | bin _ F _ => nonempty_atom F

/-- A context admits a binary formula when it admits the first argument and the second argument's
local context admits the second. -/
theorem subset_support_middleKleene_bin_iff {c : Connective} {F G : Formula Atom} {C : Set W} :
    C ⊆ Function.support ((bin c F G).middleKleene I) ↔
      C ⊆ Function.support (F.middleKleene I) ∧
        c.localContext C (F.truth I) ⊆ Function.support (G.middleKleene I) := by
  have hl (w) : w ∈ c.localContext C (F.truth I) ↔ w ∈ C ∧
      w ∈ c.localContext Set.univ (F.truth I) := by
    cases c <;> simp [Connective.localContext]
  simp only [Set.subset_def, Function.mem_support, middleKleene_bin_ne_zero I, hl, and_imp]
  exact ⟨fun h ↦ ⟨fun w hw ↦ (h w hw).1, fun w hw hc ↦ (h w hw).2 hc⟩,
    fun h w hw ↦ ⟨h.1 w hw, h.2 w hw⟩⟩

private theorem mem_ofTrivalent_middleKleene {F : Formula Atom} {C : Set W}
    (h : C ⊆ Function.support (F.middleKleene I)) :
    C ∩ F.truth I ∈ CCP.Partial.ofTrivalent (F.middleKleene I) C :=
  (CCP.Partial.mem_ofTrivalent _ _ _).2 ⟨h, Set.ext fun w ↦ and_congr_right fun hw ↦ by
    rw [middleKleene_eq_ofProp I (h hw), SignType.ofProp_eq_one_iff]⟩

private theorem ccp_spec (F : Formula Atom) : ∀ C : Set W,
    ((F.ccp I).Admits C → C ⊆ Function.support (F.middleKleene I)) ∧
      (C ⊆ Function.support (F.middleKleene I) → C ∩ F.truth I ∈ F.ccp I C) := by
  induction F with
  | atom p => exact fun C ↦ ⟨id, mem_ofTrivalent_middleKleene I⟩
  | trigger p p' => exact fun C ↦ ⟨id, mem_ofTrivalent_middleKleene I⟩
  | not F ih =>
    refine fun C ↦ ⟨fun h ↦ ?_, fun h ↦ (Part.mem_map_iff _).2 ⟨_, (ih C).2 ?_, ?_⟩⟩
    · simpa [middleKleene, eval, Set.subset_def] using (ih C).1 h
    · simpa [middleKleene, eval, Set.subset_def] using h
    · rw [Set.sdiff_self_inter, Set.sdiff_eq]; rfl
  | bin c F G ihF ihG =>
    intro C
    rw [subset_support_middleKleene_bin_iff I]
    cases c
    · refine ⟨fun ⟨hφ, hψ⟩ ↦ ?_, fun ⟨hF, hG⟩ ↦ ?_⟩
      · have hF := (ihF C).1 hφ
        beta_reduce at hψ
        rw [Part.get_eq_of_mem ((ihF C).2 hF) hφ] at hψ
        exact ⟨hF, (ihG _).1 hψ⟩
      · have hm := (ihG _).2 hG
        rw [Connective.localContext, Set.inter_assoc] at hm
        exact Part.mem_bind_iff.2 ⟨_, (ihF C).2 hF, hm⟩
    · refine ⟨fun ⟨hφ, hψ⟩ ↦ ?_, fun ⟨hF, hG⟩ ↦ ?_⟩
      · have hF := (ihF C).1 hφ
        beta_reduce at hψ
        rw [Part.get_eq_of_mem ((ihF C).2 hF) hφ] at hψ
        exact ⟨hF, (ihG _).1 hψ⟩
      · refine Part.mem_bind_iff.2 ⟨_, (ihF C).2 hF, (Part.mem_map_iff _).2 ⟨_, (ihG _).2 hG, ?_⟩⟩
        ext w
        simp only [Set.mem_sdiff, Set.mem_inter_iff, truth, Connective.eval, Set.mem_ofPred_eq]
        tauto
    · have e : C \ (C ∩ F.truth I) = Connective.disj.localContext C (F.truth I) := by
        rw [Set.sdiff_self_inter, Set.sdiff_eq]; rfl
      refine ⟨fun ⟨hφ, hψ⟩ ↦ ?_, fun ⟨hF, hG⟩ ↦ ?_⟩
      · have hF := (ihF C).1 hφ
        beta_reduce at hψ
        rw [Part.get_eq_of_mem ((ihF C).2 hF) hφ, e] at hψ
        exact ⟨hF, (ihG _).1 hψ⟩
      · refine Part.mem_bind_iff.2 ⟨_, (ihF C).2 hF, (Part.mem_map_iff _).2
          ⟨Connective.disj.localContext C (F.truth I) ∩ G.truth I,
            by rw [e]; exact (ihG _).2 hG, ?_⟩⟩
        ext w
        simp only [Connective.localContext, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
          truth, Connective.eval, Set.mem_ofPred_eq]
        tauto

/-- The context change potential of a formula admits a context iff the filtering evaluation is
defined throughout the context. -/
theorem admits_ccp_iff {F : Formula Atom} {C : Set W} :
    (F.ccp I).Admits C ↔ C ⊆ Function.support (F.middleKleene I) :=
  ⟨(ccp_spec I F C).1, fun h ↦ Part.dom_iff_mem.2 ⟨_, (ccp_spec I F C).2 h⟩⟩

/-- The context change potential updates a context to its worlds at which the formula is
classically true. -/
theorem ccp_get {F : Formula Atom} {C : Set W} (h : (F.ccp I).Admits C) :
    (F.ccp I C).get h = C ∩ F.truth I :=
  Part.get_eq_of_mem ((ccp_spec I F C).2 ((admits_ccp_iff I).1 h)) h

end Formula

/-! ### The string of a formula -/

/-- The tokens of the language as [kalomoiros-2023] writes it (Definition 3.4.1): brackets, the dot
after the antecedent of a conditional, atoms, triggers, *not* and the connective words. A trigger
`p′p` is one token. -/
inductive Token (Atom : Type*) where
  | lparen
  | rparen
  | dot
  | atom (p : Atom)
  | trigger (presup assert : Atom)
  | not
  | conn (c : Connective)
  deriving DecidableEq

namespace Token

/-- The tokens of a binary formula before its first argument, after the bracket: *if* for a
conditional and nothing otherwise. -/
def lead : Connective → List (Token Atom)
  | .cond => [.conn .cond]
  | _ => []

/-- The token between the arguments of a binary formula: the dot after a conditional's antecedent,
and otherwise the connective word. -/
def sep : Connective → Token Atom
  | .cond => .dot
  | c => .conn c

end Token

namespace Formula

/-- The string of a formula: `p`, `p′p`, `(not F)`, `(F and G)`, `(F or G)` and `(if F. G)`. -/
def yield : Formula Atom → List (Token Atom)
  | atom p => [.atom p]
  | trigger p p' => [.trigger p p']
  | not F => .lparen :: .not :: (F.yield ++ [.rparen])
  | bin c F G => .lparen :: (Token.lead c ++ (F.yield ++ Token.sep c :: (G.yield ++ [.rparen])))

/-- The rest of a binary formula after its opening bracket, parsing its arguments with `p`: a
formula, a connective word, a formula and a closing bracket. -/
def parseBinary (p : List (Token Atom) → Option (Formula Atom × List (Token Atom)))
    (ts : List (Token Atom)) : Option (Formula Atom × List (Token Atom)) := do
  let (F, .conn c :: ts) ← p ts | none
  let (G, .rparen :: ts) ← p ts | none
  pure (bin c F G, ts)

/-- Parse a formula from the front of a string, nesting at most `n` formulas, and return it with
the rest of the string: a computation of the state monad of the remaining tokens over `Option`. -/
def parse : ℕ → List (Token Atom) → Option (Formula Atom × List (Token Atom))
  | 0, _ => none
  | _ + 1, .atom p :: ts => some (atom p, ts)
  | _ + 1, .trigger p p' :: ts => some (trigger p p', ts)
  | n + 1, .lparen :: .not :: ts => do
    let (F, .rparen :: ts) ← parse n ts | none
    pure (not F, ts)
  | n + 1, .lparen :: .conn .cond :: ts => do
    let (F, .dot :: ts) ← parse n ts | none
    let (G, .rparen :: ts) ← parse n ts | none
    pure (bin .cond F G, ts)
  | n + 1, .lparen :: ts => parseBinary (parse n) ts
  | _ + 1, _ => none

theorem yield_ne_nil (F : Formula Atom) : F.yield ≠ [] := by
  cases F <;> simp [yield]

/-- A formula's string begins with an atom, a trigger or a bracket, never with *not*. -/
theorem yield_append_ne_not (F : Formula Atom) (r r' : List (Token Atom)) :
    F.yield ++ r ≠ .not :: r' := by
  cases F <;> simp [yield]

/-- A formula's string never begins with a connective word. -/
theorem yield_append_ne_conn (F : Formula Atom) (c : Connective) (r r' : List (Token Atom)) :
    F.yield ++ r ≠ .conn c :: r' := by
  cases F <;> simp [yield]

private theorem parse_lparen (n : ℕ) {ts : List (Token Atom)} (h₁ : ∀ ts', ts ≠ .not :: ts')
    (h₂ : ∀ ts', ts ≠ .conn .cond :: ts') :
    parse (n + 1) (.lparen :: ts) = parseBinary (parse n) ts := by
  rcases ts with _ | ⟨t, ts⟩
  · rfl
  · cases t with
    | not => exact absurd rfl (h₁ ts)
    | conn c => cases c <;> first | exact absurd rfl (h₂ ts) | rfl
    | _ => rfl

/-- Parsing the string of a formula gives back the formula and the rest of the string. -/
theorem parse_yield (F : Formula Atom) {n : ℕ} (r : List (Token Atom))
    (hn : F.yield.length ≤ n) : parse n (F.yield ++ r) = some (F, r) := by
  induction F generalizing n r with
  | atom p => obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [yield] at hn; omega⟩; rfl
  | trigger p p' => obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [yield] at hn; omega⟩; rfl
  | not F ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [yield] at hn; omega⟩
    simp only [yield, List.length_cons, List.length_append] at hn
    simp [yield, parse, ih (.rparen :: r) (show F.yield.length ≤ n by simp at hn; omega)]
  | bin c F G ihF ihG =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [yield] at hn; omega⟩
    have hF : F.yield.length ≤ n := by cases c <;> simp [yield, Token.lead] at hn <;> omega
    have hG : G.yield.length ≤ n := by cases c <;> simp [yield, Token.lead] at hn <;> omega
    cases c with
    | cond => simp [yield, Token.lead, Token.sep, parse, ihF _ hF, ihG _ hG]
    | _ =>
      simp only [yield, Token.lead, Token.sep, List.nil_append, List.cons_append,
        List.append_assoc]
      rw [parse_lparen n (fun _ ↦ yield_append_ne_not F _ _)
        (fun _ ↦ yield_append_ne_conn F _ _ _)]
      simp [parseBinary, ihF _ hF, ihG _ hG]

/-- Unique readability: a formula's string determines the formula, even followed by more
tokens. -/
theorem yield_append_inj {F F' : Formula Atom} {r r' : List (Token Atom)}
    (h : F.yield ++ r = F'.yield ++ r') : F = F' ∧ r = r' := by
  have := (parse_yield F r (le_max_left _ F'.yield.length)).symm.trans
    (h ▸ parse_yield F' r' (le_max_right F.yield.length _))
  simpa using this

/-- A formula's string determines the formula. -/
theorem yield_injective : Function.Injective (yield : Formula Atom → List (Token Atom)) :=
  fun F F' h ↦ (yield_append_inj (r := []) (r' := []) (by simpa using h)).1

end Formula

end Presupposition
