module

public import Linglib.Data.Examples.Snyder2026
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Reference.Iota
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Composition.Sorts

/-!
# Snyder (2026): Numbers as Kinds

Polymorphic Contextualism takes the lexical meaning of *two* to be an atomic predicate, true of
whatever falls under the kind TWO, whether a numeral token, a subkind such as the two of the
naturals, or TWO itself, and derives every other meaning by type-shifting. Its rivals start from a
numeral (Substantivalism) or from a cardinality predicate (Adjectivalism). The three are derivation
maps through the type-shifters CARD, PM, A, NOM, IOTA and IDENT, each of which [composes to the type
of the function it derives](##analyses_well_typed), and only Contextualism [reaches the token, kind
and taxonomic uses](##contextualism_strictly_extends). The numeral is the definite of the lexical
predicate among the atoms a context makes salient. A close appositive whose modifier names a number
system [refers to the subkind of that system](##subkind_mem_iota_lex_inter_system), appositives
naming different systems [refer to different subkinds](##ne_of_mem_iota_lex_inter_system), so that
both answers to Benacerraf's question can be true, and with no system in play [nothing is referred
to](##iota_lex_inter_range_subkind_eq_none).

## Implementation notes

* Types are the fragment e, ⟨e,t⟩ and ⟨⟨e,t⟩,t⟩; PM is monadic, its second predicate supplied
  by the syntax. Rothstein's schematic equation is a meta-level identification and not a
  type-shifter, so the adjectivalist numeral is the nominalized cardinality predicate with the
  equation read off it.
* In the contextualist diagram the token, kind and taxonomic uses (76h), (76j) and (76f) are
  the lexical predicate itself, applied to tokens or kinds, and the numeral, kind-referring
  and token-referring uses (76e), (76i) and (76g) are IOTA over it; the taxonomic use is
  predicate-typed, the others entity-typed.
* The atoms are the tokens, subkinds and kinds of any three types, with a map `inst` from a
  token to the subkind it instantiates and a map `sup` from a subkind to its kind. A context is
  the set of atoms it makes salient, and the definite of (16) and (74) is `iota`, undefined when
  no atom or several are salient.
* The partitions of section 4.3, of tokens by the number they represent and of numbers by their
  system, are the kernels of `inst` and of the system map. On the board a number is a pair of a
  system and a value, so a system and a kind determine a subkind.
* The colour words of the conclusion are the same theorems at other types, the shades of red in
  place of the subkinds of TWO.

## TODO

* The derivation maps transcribe the paper's diagrams, and the rivals' gaps are read off them.
  Deriving the gaps from the context-invariant referent the rivals assign to the numeral is not
  done.

## References

* [snyder-2026]
* [mendia-2020]
* [sharvy-1980]
* [partee-1987]
* [benacerraf-1965]
-/

@[expose] public section

namespace Snyder2026

open Interpreter

/-! ### The three polymorphic analyses and the semantic functions -/

/-- The three polymorphic analyses: the lexical meaning of *two* is a numeral (5), a
cardinality predicate (9), or an atomic predicate over relativized atoms (73). -/
inductive PolymorphicAnalysis
  | substantivalism | adjectivalism | contextualism
  deriving DecidableEq

/-- The lexical type of *two* under each analysis. -/
def PolymorphicAnalysis.lexicalType : PolymorphicAnalysis → Ty Base
  | .substantivalism => .e
  | .adjectivalism => .et
  | .contextualism => .et

/-- The semantic functions of *two*: the six of (1) and the token, kind and taxonomic uses of
(76g) to (76j). -/
inductive SemanticFunction
  | predicative | attributive | quantificational | specificational | numeral | closeAppositive
  | tokenRef | tokenPredicate | kindRef | taxonomic
  deriving DecidableEq

/-- The type at which each function is used. -/
def SemanticFunction.targetType : SemanticFunction → Ty Base
  | .predicative | .attributive | .tokenPredicate | .taxonomic => .et
  | .quantificational => .ett
  | .specificational | .numeral | .closeAppositive | .tokenRef | .kindRef => .e

/-- The label of a function in the example rows. -/
def SemanticFunction.label : SemanticFunction → String
  | .predicative => "predicative"
  | .attributive => "attributive"
  | .quantificational => "quantificational"
  | .specificational => "specificational"
  | .numeral => "numeral"
  | .closeAppositive => "closeAppositive"
  | .tokenRef => "tokenRef"
  | .tokenPredicate => "tokenPredicate"
  | .kindRef => "kindRef"
  | .taxonomic => "taxonomic"

/-- The type-shifters of the diagrams: CARD (6a), Predicate Modification (7a), A (8a), NOM
(10a), IOTA (74a) and IDENT (17a). -/
inductive Operator
  | card | pm | a | nom | iota | ident
  deriving DecidableEq

/-- The input type of a type-shifter. -/
def Operator.input : Operator → Ty Base
  | .card | .ident => .e
  | .pm | .a | .nom | .iota => .et

/-- The output type of a type-shifter. -/
def Operator.output : Operator → Ty Base
  | .card | .pm | .ident => .et
  | .a => .ett
  | .nom | .iota => .e

/-- The type a chain of type-shifters reaches from a type, if each composes with the last. -/
def wellTyped (τ : Ty Base) (ops : List Operator) : Option (Ty Base) :=
  ops.foldlM (fun τ op ↦ if τ = op.input then some op.output else none) τ

/-- The derivation map of each analysis, the diagrams of sections 2 and 5: the chain of
type-shifters from the lexical meaning to a function, or none where the analysis does not
derive it. Substantivalism derives the cardinal uses by CARD and the close appositive by IDENT
and IOTA; Adjectivalism nominalizes the cardinality predicate for the numeral and passes
through it for the close appositive; Contextualism reaches the numeral, kind and token
references by IOTA, the taxonomic and token predications by the lexical predicate itself, the
cardinal uses through the numeral, and the close appositive by PM with *number* and IOTA (87). -/
def PolymorphicAnalysis.path : PolymorphicAnalysis → SemanticFunction → Option (List Operator)
  | .substantivalism, .numeral => some []
  | .substantivalism, .predicative => some [.card]
  | .substantivalism, .attributive => some [.card, .pm]
  | .substantivalism, .quantificational => some [.card, .a]
  | .substantivalism, .specificational => some [.card, .nom]
  | .substantivalism, .closeAppositive => some [.ident, .iota]
  | .substantivalism, _ => none
  | .adjectivalism, .predicative => some []
  | .adjectivalism, .attributive => some [.pm]
  | .adjectivalism, .quantificational => some [.a]
  | .adjectivalism, .specificational => some [.nom]
  | .adjectivalism, .numeral => some [.nom]
  | .adjectivalism, .closeAppositive => some [.nom, .ident, .iota]
  | .adjectivalism, _ => none
  | .contextualism, .taxonomic => some []
  | .contextualism, .tokenPredicate => some []
  | .contextualism, .numeral => some [.iota]
  | .contextualism, .kindRef => some [.iota]
  | .contextualism, .tokenRef => some [.iota]
  | .contextualism, .predicative => some [.iota, .card]
  | .contextualism, .attributive => some [.iota, .card, .pm]
  | .contextualism, .quantificational => some [.iota, .card, .a]
  | .contextualism, .specificational => some [.iota, .card, .nom]
  | .contextualism, .closeAppositive => some [.pm, .iota]

/-- An analysis covers a function when it derives it. -/
def PolymorphicAnalysis.Covers (a : PolymorphicAnalysis) (sf : SemanticFunction) : Prop :=
  (a.path sf).isSome

instance (a : PolymorphicAnalysis) (sf : SemanticFunction) : Decidable (a.Covers sf) :=
  inferInstanceAs (Decidable (_ = true))

theorem analyses_well_typed (a : PolymorphicAnalysis) (sf : SemanticFunction) :
    ∀ ops ∈ a.path sf, wellTyped a.lexicalType ops = some sf.targetType := by
  cases a <;> cases sf <;> decide

theorem contextualism_covers_all (sf : SemanticFunction) :
    PolymorphicAnalysis.contextualism.Covers sf := by
  cases sf <;> decide

theorem substantivalism_gap :
    ∀ sf ∈ [SemanticFunction.tokenRef, .tokenPredicate, .kindRef, .taxonomic],
      ¬ PolymorphicAnalysis.substantivalism.Covers sf := by
  decide

theorem adjectivalism_gap :
    ∀ sf ∈ [SemanticFunction.tokenRef, .tokenPredicate, .kindRef, .taxonomic],
      ¬ PolymorphicAnalysis.adjectivalism.Covers sf := by
  decide

theorem contextualism_strictly_extends (a : PolymorphicAnalysis) :
    (∀ sf, a.Covers sf → PolymorphicAnalysis.contextualism.Covers sf) ∧
      (a ≠ .contextualism → ∃ sf, PolymorphicAnalysis.contextualism.Covers sf ∧ ¬ a.Covers sf) :=
  ⟨fun sf _ ↦ contextualism_covers_all sf, fun h ↦ ⟨.taxonomic, contextualism_covers_all _,
    by cases a <;> first | exact absurd rfl h | decide⟩⟩

/-! ### Numbers as kinds (sections 4 and 5) -/

section Kinds

variable {T N V σ : Type*}

/-- The atoms of relativized atomicity: a token, the subkind it instantiates, and the kind that
subkind falls under each count as one. -/
inductive Atom (T N V : Type*)
  | token (t : T)
  | subkind (n : N)
  | kind (v : V)

variable (inst : T → N) (sup : N → V) {v : V}

/-- The kind an atom falls under: that of the subkind a token instantiates, that of a subkind, or
the kind itself. -/
def Atom.kindOf : Atom T N V → V
  | .token t => sup (inst t)
  | .subkind n => sup n
  | .kind v => v

/-- (73): the lexical extension of a number word is the atoms that fall under its kind, whether
tokens, subkinds, or the kind itself. -/
def lex (v : V) : Set (Atom T N V) := Atom.kindOf inst sup ⁻¹' {v}

-- (86), `snyder2026_76g`: a context with one salient atom
theorem iota_lex_inter_singleton {a : Atom T N V} (ha : a ∈ lex inst sup v) :
    iota (lex inst sup v ∩ {a}) = Part.some a := by
  rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ha), iota_singleton]

-- (47d), `snyder2026_4b`: a context of kinds
theorem iota_lex_inter_range_kind (v : V) :
    iota (lex inst sup v ∩ Set.range Atom.kind) = Part.some (.kind v) := by
  have : lex inst sup v ∩ Set.range Atom.kind = {.kind v} := by
    ext a
    cases a <;> simp [lex, Atom.kindOf, eq_comm]
  rw [this, iota_singleton]

theorem subkind_mem_iota_lex_inter_image {M : Set N} {n : N} :
    Atom.subkind n ∈ iota (lex inst sup v ∩ Atom.subkind '' M) ↔ n ∈ iota (M ∩ sup ⁻¹' {v}) := by
  simp only [mem_iota, Set.mem_inter_iff, Set.mem_image, Atom.subkind.injEq, exists_eq_right,
    Set.mem_preimage, Set.mem_singleton_iff, lex, Atom.kindOf, and_imp, forall_exists_index]
  exact ⟨fun ⟨⟨hv, hn⟩, hu⟩ ↦ ⟨⟨hn, hv⟩, fun m hm hmv ↦ Atom.subkind.inj (hu _ hmv m hm rfl)⟩,
    fun ⟨⟨hn, hv⟩, hu⟩ ↦ ⟨⟨hv, hn⟩, fun _ hmv m hm e ↦ by subst e; exact congrArg _ (hu m hm hmv)⟩⟩

/-- When a system and a kind together determine a subkind, the close appositive whose modifier
names the system of `n` refers to `n`, as *the natural number two* refers to the two of the
naturals (87). -/
theorem subkind_mem_iota_lex_inter_system (sys : N → σ)
    (h : Function.Injective fun n ↦ (sys n, sup n)) (n : N) :
    Atom.subkind n ∈ iota (lex inst sup (sup n) ∩ Atom.subkind '' (sys ⁻¹' {sys n})) :=
  (subkind_mem_iota_lex_inter_image inst sup).2 <| mem_iota.2
    ⟨⟨rfl, rfl⟩, fun _ hm ↦ h (Prod.ext hm.1 hm.2)⟩

/-- Close appositives whose modifiers name different systems refer to different subkinds, so
*the von Neumann ordinal two* and *the Zermelo ordinal two* need not corefer ((20), (83)). -/
theorem ne_of_mem_iota_lex_inter_system (sys : N → σ) {s₁ s₂ : σ} (h : s₁ ≠ s₂)
    {a₁ a₂ : Atom T N V}
    (h₁ : a₁ ∈ iota (lex inst sup v ∩ Atom.subkind '' (sys ⁻¹' {s₁})))
    (h₂ : a₂ ∈ iota (lex inst sup v ∩ Atom.subkind '' (sys ⁻¹' {s₂}))) : a₁ ≠ a₂ := by
  obtain ⟨n₁, hn₁, rfl⟩ := (mem_iota.1 h₁).1.2
  obtain ⟨n₂, hn₂, rfl⟩ := (mem_iota.1 h₂).1.2
  exact fun e ↦ h (hn₁.symm.trans ((congrArg sys (Atom.subkind.inj e)).trans hn₂))

/-- Without a modifier or a salient system, *the number two* has no referent when two subkinds
fall under the kind (87). -/
theorem iota_lex_inter_range_subkind_eq_none {n m : N} (hn : sup n = v) (hm : sup m = v)
    (hne : n ≠ m) : iota (lex inst sup v ∩ Set.range Atom.subkind) = Part.none :=
  iota_eq_none_of_ne (e := .subkind n) (e' := .subkind m) ⟨hn, n, rfl⟩ ⟨hm, m, rfl⟩
    fun e ↦ hne (Atom.subkind.inj e)

-- (85b), (85c): the tokens of one subkind are several tokens and one type
theorem ncard_image_inst_eq_one {X : Set T} (hX : X.Nonempty)
    (h : ∀ x ∈ X, ∀ y ∈ X, inst x = inst y) : (inst '' X).ncard = 1 :=
  let ⟨a, ha⟩ := hX
  Set.ncard_eq_one.2 ⟨inst a, Set.eq_singleton_iff_unique_mem.2
    ⟨⟨a, ha, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact h x hx a ha⟩⟩

end Kinds

/-! ### The numbers of the board (section 4.3) -/

/-- The number systems of the board. -/
inductive MathSystem
  | nat | rat | real
  deriving DecidableEq

/-- The numbers a token on the board may represent. -/
inductive Value
  | one | two
  deriving DecidableEq

-- (81), (82), `snyder2026_1e`
theorem subkind_mem_iota_lex_inter_system_board (s : MathSystem) :
    (Atom.subkind (s, Value.two) : Atom ((MathSystem × Value) × ℕ) (MathSystem × Value) Value) ∈
      iota (lex Prod.fst Prod.snd Value.two ∩ Atom.subkind '' (Prod.fst ⁻¹' {s})) :=
  subkind_mem_iota_lex_inter_system Prod.fst Prod.snd Prod.fst (fun _ _ h ↦ h) (s, Value.two)

/-! ### The examples -/

theorem functions_attested (sf : SemanticFunction) :
    ∃ ex ∈ Examples.all, ex.feature? "function" = some sf.label := by
  cases sf <;> decide

end Snyder2026
