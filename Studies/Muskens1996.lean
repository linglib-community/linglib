module

public import Linglib.Semantics.Dynamic.DRS.Dynamics
public import Linglib.Semantics.Dynamic.RegisterStructure
public import Mathlib.Data.Fin.VecNotation

/-!
# Muskens (1996): Combining Montague semantics and discourse representation

Muskens treats the boxes of discourse representation theory as relations between states, so
that word meanings combine by function application and sequencing as in Montague semantics.
This file gives his lexicon over the register structures of
`Semantics/Dynamic/RegisterStructure.lean` and computes the meanings of his example sentences.

## Main statements

* `text_eq_box`: "A man adores a woman. She abhors him." means a single box introducing both
  referents.
* `dom_text`, `dom_conditional`, `dom_vpCoord`, `dom_npCoord`, `dom_reassignment`: the examples
  have the first-order truth conditions the paper gives.
* `dom_everyNarrow`, `dom_everyWide`: "Every girl adores a boy" has both scope readings.
* `dom_npCoord_no`: a pronoun after a conjunct headed by `no` reads its referent off the input
  state, so `no` does not bind it.
* `reassignment_ne_merge`: "Bill and Sue own a donkey" reassigns the donkey's referent, and its
  two boxes do not merge into one.
* `toRel_improper_eq`, `not_isProper_improper`: a proper and an improper box can mean the same,
  so properness is a property of representations.
* `fn4_diverges`: declaring a referent twice separates Muskens's semantics from Kamp and
  Reyle's.

## Implementation notes

Static predicates are sets, so an atomic condition is a preimage. A dynamic predicate takes the
value function of a referent rather than its register, and names, pronouns and traces mean
`Function.eval δ` for their referent `δ`. Conjunction at every category is the product of the
update monoid lifted pointwise, so conjoined verb phrases and noun phrases multiply with `*`.

## TODO

* Muskens's box language with sequencing, its translation into first-order logic, and his
  propositions about that translation. The one relating properness to closed formulas needs the
  free variables of `DRS.toFormula`, which mathlib does not yet compute for `relabel` and
  `iExs`.

## References

* [muskens-1996]
* [kamp-reyle-1993]
-/

@[expose] public section

namespace Muskens1996

open DynamicSemantics Update SetRel RegisterStructure

variable {R S E : Type*}

/-! ### The lexicon -/

/-- A dynamic predicate, the meaning of a noun or verb phrase, takes a discourse referent to an
update. -/
abbrev DynPred (S E : Type*) := (S → E) → Update S

/-- A dynamic quantifier, the meaning of a noun phrase, takes a dynamic predicate to an update. -/
abbrev DynQuant (S E : Type*) := DynPred S E → Update S

/-- A common noun or intransitive verb translates as the test of its predicate, as in
`farmer ↝ λv[|farmer v]` and `stink ↝ λv[|stinks v]`. -/
def ofStatic (P : Set E) : DynPred S E :=
  fun v ↦ test (v ⁻¹' P)

/-- A transitive verb takes its object noun phrase, as in `love ↝ λQλv(Q(λv'[|v loves v']))`.
-/
def ofStatic₂ (P : SetRel E E) : DynQuant S E → DynPred S E :=
  fun Q v ↦ Q fun v' ↦ test {i | v i ~[P] v' i}

/-- A name translates as the lift of the constant referent that AX4 gives it, as in
`Maryⁿ ↝ λP.P(Mary)`. -/
def name (x : E) : DynQuant S E :=
  Function.eval (Function.const S x)

section Determiners

variable [RegisterStructure R S E]

/-- The indefinite, `aⁿ ↝ λP'λP([uₙ|]; P'(uₙ); P(uₙ))`. -/
def indef (u : R) : DynPred S E → DynQuant S E :=
  fun P' P ↦ randomAssign u ○ (P' (val u) ○ P (val u))

/-- The universal, `everyⁿ ↝ λP'λP[|([uₙ|]; P'(uₙ)) ⇒ P(uₙ)]`. -/
def every (u : R) : DynPred S E → DynQuant S E :=
  fun P' P ↦ test (impl (randomAssign u ○ P' (val u)) (P (val u)))

/-- The negative determiner, `noⁿ ↝ λP'λP[|not([uₙ|]; P'(uₙ); P(uₙ))]`. -/
def no (u : R) : DynPred S E → DynQuant S E :=
  fun P' P ↦ test (neg (randomAssign u ○ (P' (val u) ○ P (val u))))

end Determiners

/-- The relative pronoun takes the relative clause and then the noun, as in
`who ↝ λP'λPλv(P(v); P'(v))`. -/
def who : DynPred S E → DynPred S E → DynPred S E :=
  fun P' P v ↦ P v ○ P' v

/-- Auxiliary negation, `doesn't ↝ λPλQ[|not Q(P)]`. -/
def doesnt : DynPred S E → DynQuant S E → Update S :=
  fun P Q ↦ test (neg (Q P))

/-- The conditional, `if ↝ λpq[|p ⇒ q]`. -/
def ifThen : Update S → Update S → Update S :=
  fun p q ↦ test (impl p q)

/-! ### The paper's derivations -/

section Derivations

variable [RegisterStructure R S E] {u₁ u₂ : R}

attribute [local simp] ofStatic ofStatic₂ Function.eval name indef no who ifThen Pi.mul_apply
  mul_def dom_comp preimage_comp preimage_randomAssign val_extend_self

/-- "A¹ man adores a² woman. She₂ abhors him₁." ((9); its first sentence is tree (39)). -/
def text (u₁ u₂ : R) (man woman : Set E) (adores abhors : SetRel E E) : Update S :=
  indef u₁ (ofStatic man) (ofStatic₂ adores (indef u₂ (ofStatic woman))) ○
    Function.eval (val u₂) (ofStatic₂ abhors (Function.eval (val u₁)))

/-- The text reduces by merging to the box (20). -/
theorem text_eq_box [DecidableEq R] (h : u₁ ≠ u₂) (man woman : Set E) (adores abhors : SetRel E E) :
    (text u₁ u₂ man woman adores abhors : Update S) =
      box {u₁, u₂} (val u₁ ⁻¹' man ∩ (val u₂ ⁻¹' woman ∩ {i | val u₁ i ~[adores] val u₂ i}) ∩
        {i | val u₂ i ~[abhors] val u₁ i}) := by
  have : (text u₁ u₂ man woman adores abhors : Update S) =
      box {u₁} (val u₁ ⁻¹' man) ○ box {u₂} (val u₂ ⁻¹' woman ∩ {i | val u₁ i ~[adores] val u₂ i}) ○
        box (∅ : Finset R) {i | val u₂ i ~[abhors] val u₁ i} := by
    simp only [text, indef, ofStatic, ofStatic₂, Function.eval, box_singleton, dexists, box_empty,
      ← test_comp_test, comp_assoc]
  rw [this, box_comp_box (by simpa using fun hu ↦ h.symm (dimSet_preimage_val_subset u₁ man hu)),
    box_comp_box (by simp), Finset.union_empty]
  rfl

/-- The truth conditions (24) of the text. -/
theorem dom_text (h : u₁ ≠ u₂) (man woman : Set E) (adores abhors : SetRel E E) :
    (text u₁ u₂ man woman adores abhors : Update S).dom =
      {_i | ∃ x₁ x₂, x₁ ∈ man ∧ x₂ ∈ woman ∧ x₁ ~[adores] x₂ ∧ x₂ ~[abhors] x₁} := by
  ext
  simp [text, val_extend_of_ne _ _ _ _ h, and_assoc]

/-- "Every¹ girl adores a² boy" ((33)) at its S-structure (34), the indefinite in situ. -/
def everyNarrow (u₁ u₂ : R) (girl boy : Set E) (adores : SetRel E E) : Update S :=
  every u₁ (ofStatic girl) (ofStatic₂ adores (indef u₂ (ofStatic boy)))

/-- At the LF (35), decorated as (40), (33) quantifies `a² boy` in over the trace `e₃`. -/
def everyWide (u₁ u₂ : R) (girl boy : Set E) (adores : SetRel E E) : Update S :=
  indef u₂ (ofStatic boy) fun v₃ ↦ every u₁ (ofStatic girl) (ofStatic₂ adores (Function.eval v₃))

/-- The `∀∃` reading of (33), from (34). -/
theorem dom_everyNarrow (h : u₁ ≠ u₂) (girl boy : Set E) (adores : SetRel E E) :
    (everyNarrow u₁ u₂ girl boy adores : Update S).dom =
      {_i | ∀ x₁ ∈ girl, ∃ x₂ ∈ boy, x₁ ~[adores] x₂} := by
  ext
  simp [everyNarrow, every, impl, core_comp, core_randomAssign, core_test,
    val_extend_of_ne _ _ _ _ h, or_iff_not_imp_left]

/-- The `∃∀` reading of (33) comes from (35), with the indefinite's referent available to a later
pronoun ((41)). -/
theorem dom_everyWide (h : u₁ ≠ u₂) (girl boy : Set E) (adores : SetRel E E) :
    (everyWide u₁ u₂ girl boy adores : Update S).dom =
      {_i | ∃ x₂ ∈ boy, ∀ x₁ ∈ girl, x₁ ~[adores] x₂} := by
  ext
  simp [everyWide, every, impl, core_comp, core_randomAssign, core_test,
    val_extend_of_ne _ _ _ _ h.symm, or_iff_not_imp_left]

/-- "If a¹ man bores a² woman she₂ ignores him₁." ((4), translated as the box (6)). -/
def conditional (u₁ u₂ : R) (man woman : Set E) (bores ignores : SetRel E E) : Update S :=
  ifThen (indef u₁ (ofStatic man) (ofStatic₂ bores (indef u₂ (ofStatic woman))))
    (Function.eval (val u₂) (ofStatic₂ ignores (Function.eval (val u₁))))

/-- The conditional has the truth conditions (8), in which the indefinites of the antecedent
bind the pronouns of the consequent with universal force. -/
theorem dom_conditional (h : u₁ ≠ u₂) (man woman : Set E) (bores ignores : SetRel E E) :
    (conditional u₁ u₂ man woman bores ignores : Update S).dom =
      {_i | ∀ x₁ x₂, x₁ ∈ man ∧ x₂ ∈ woman ∧ x₁ ~[bores] x₂ → x₂ ~[ignores] x₁} := by
  ext
  simp [conditional, impl, core_comp, core_randomAssign, core_test, val_extend_of_ne _ _ _ _ h]
  grind

/-- "A² cat catches a¹ fish and eats it₁." ((52), decorated as tree (56)). The conjoined VPs are
sequenced, so the referent of `a¹ fish` is accessible to `it₁`. -/
def vpCoord (u₁ u₂ : R) (cat fish : Set E) (catches eats : SetRel E E) : Update S :=
  indef u₂ (ofStatic cat) (ofStatic₂ catches (indef u₁ (ofStatic fish)) *
    ofStatic₂ eats (Function.eval (val u₁)))

/-- The truth conditions of (52). -/
theorem dom_vpCoord (h : u₁ ≠ u₂) (cat fish : Set E) (catches eats : SetRel E E) :
    (vpCoord u₁ u₂ cat fish catches eats : Update S).dom =
      {_i | ∃ x₂ x₁, x₂ ∈ cat ∧ x₁ ∈ fish ∧ x₂ ~[catches] x₁ ∧ x₂ ~[eats] x₁} := by
  ext
  simp [vpCoord, val_extend_of_ne _ _ _ _ h.symm, and_assoc]

/-- "John³ admires a¹ girl and a² boy who loves her₁." ((58), with the conjoined NP of (57)). -/
def npCoord (u₁ u₂ : R) (john : E) (girl boy : Set E) (admires loves : SetRel E E) : Update S :=
  name john (ofStatic₂ admires (indef u₁ (ofStatic girl) *
    indef u₂ (who (ofStatic₂ loves (Function.eval (val u₁))) (ofStatic boy))))

/-- The truth conditions (60) of (58). -/
theorem dom_npCoord (h : u₁ ≠ u₂) (john : E) (girl boy : Set E) (admires loves : SetRel E E) :
    (npCoord u₁ u₂ john girl boy admires loves : Update S).dom =
      {_i | ∃ x₁ x₂, x₁ ∈ girl ∧ john ~[admires] x₁ ∧ x₂ ∈ boy ∧ x₂ ~[loves] x₁ ∧
        john ~[admires] x₂} := by
  ext
  simp [npCoord, val_extend_of_ne _ _ _ _ h, and_assoc]

/-- "*John³ admires no¹ girl and a² boy who loves her₁." ((61)), in which `no¹` cannot bind
`her₁`. -/
def npCoordNo (u₁ u₂ : R) (john : E) (girl boy : Set E) (admires loves : SetRel E E) :
    Update S :=
  name john (ofStatic₂ admires (no u₁ (ofStatic girl) *
    indef u₂ (who (ofStatic₂ loves (Function.eval (val u₁))) (ofStatic boy))))

/-- The truth conditions (65) of (61) are an open formula, which reads the pronoun's referent
off the input state. -/
theorem dom_npCoord_no (h : u₁ ≠ u₂) (john : E) (girl boy : Set E) (admires loves : SetRel E E) :
    (npCoordNo u₁ u₂ john girl boy admires loves : Update S).dom =
      {i | ∃ x₂, (¬∃ x₁ ∈ girl, john ~[admires] x₁) ∧ x₂ ∈ boy ∧ x₂ ~[loves] val u₁ i ∧
        john ~[admires] x₂} := by
  ext
  simp [npCoordNo, mem_randomAssign, val_extend_of_ne _ _ _ _ h, and_assoc]

/-- "Bill¹ and Sue² own a³ donkey." ((66)), with the conjoined names applied pointwise. -/
def reassignment (u₃ : R) (bill sue : E) (donkey : Set E) (owns : SetRel E E) : Update S :=
  (name bill * name sue : DynQuant S E) (ofStatic₂ owns (indef u₃ (ofStatic donkey)))

-- (66), (67)
theorem reassignment_eq (u₃ : R) (bill sue : E) (donkey : Set E) (owns : SetRel E E) :
    (reassignment u₃ bill sue donkey owns : Update S) =
      box {u₃} (val u₃ ⁻¹' donkey ∩ {i | bill ~[owns] val u₃ i}) ○
        box {u₃} (val u₃ ⁻¹' donkey ∩ {i | sue ~[owns] val u₃ i}) := by
  simp only [reassignment, name, Function.const_apply, Pi.mul_apply, mul_def, Function.eval,
    ofStatic₂, indef, ofStatic, box_singleton, dexists, ← test_comp_test, comp_assoc]

/-- The truth conditions (68) of (66). -/
theorem dom_reassignment (u₃ : R) (bill sue : E) (donkey : Set E) (owns : SetRel E E) :
    (reassignment u₃ bill sue donkey owns : Update S).dom =
      {_i | (∃ x₃ ∈ donkey, bill ~[owns] x₃) ∧ ∃ x₃ ∈ donkey, sue ~[owns] x₃} := by
  ext
  simp [reassignment]

/-- The boxes of (67) do not merge when Bill and Sue own only different donkeys. -/
theorem reassignment_ne_merge [Nonempty S] {u₃ : R} {bill sue : E} {donkey : Set E}
    {owns : SetRel E E} (hb : ∃ x ∈ donkey, bill ~[owns] x) (hs : ∃ x ∈ donkey, sue ~[owns] x)
    (h : ¬∃ x ∈ donkey, bill ~[owns] x ∧ sue ~[owns] x) :
    (reassignment u₃ bill sue donkey owns : Update S) ≠
      box {u₃} ((val u₃ ⁻¹' donkey ∩ {i | bill ~[owns] val u₃ i}) ∩
        (val u₃ ⁻¹' donkey ∩ {i | sue ~[owns] val u₃ i})) := by
  intro heq
  obtain ⟨i⟩ := ‹Nonempty S›
  have hi : i ∈ (reassignment u₃ bill sue donkey owns : Update S).dom := by
    rw [dom_reassignment]
    exact ⟨hb, hs⟩
  rw [heq, box_singleton, dom_dexists, dom_test] at hi
  obtain ⟨_, ⟨hd, hbo⟩, -, hso⟩ := hi
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, val_extend_self] at hd hbo hso
  exact h ⟨_, hd, hbo, hso⟩

end Derivations

/-! ### Properness is representational (§III.5)

A proper box and a box that is not proper may have the same semantic value: (45), the
translation of "No¹ girl walks", and (47), that of "*No¹ girl walks. If she₁ talks she₁ talks",
denote the same relation in every model, but only (45) is proper. Acceptability of an indexing
is therefore a property of its representation, which is why Muskens simplifies translations by
lambda conversion and merging only. -/

section Representational

open FirstOrder FirstOrder.Language DRT

/-- The relation symbols of (44)–(47) are `girl`, `walk` and `talk`. -/
inductive GirlRel : ℕ → Type
  | girl : GirlRel 1
  | walk : GirlRel 1
  | talk : GirlRel 1

/-- The language of (44)–(47). -/
def girlLang : Language := ⟨fun _ ↦ Empty, GirlRel⟩

/-- `[u₁ | girl u₁, walk u₁]`. -/
def girlWalks : DRS girlLang ℕ := .mk {1} [.atom ⟨.girl, ![1]⟩, .atom ⟨.walk, ![1]⟩]

/-- `[ | talk u₁]`. -/
def talks : DRS girlLang ℕ := .mk ∅ [.atom ⟨.talk, ![1]⟩]

/-- The box (45) is `[ | not[u₁ | girl u₁, walk u₁]]`. -/
def proper : DRS girlLang ℕ := .mk ∅ [.neg girlWalks]

/-- The box (47) is `[ | not[u₁ | girl u₁, walk u₁], [ | talk u₁] ⇒ [ | talk u₁]]`. -/
def improper : DRS girlLang ℕ := .mk ∅ [.neg girlWalks, .imp talks talks]

theorem isProper_proper : proper.IsProper := by decide

theorem not_isProper_improper : ¬ improper.IsProper := by decide

/-- (45) and (47) denote the same relation in every model. -/
theorem toRel_improper_eq {M : Type*} [girlLang.Structure M] :
    (DRS.toRel improper : Update (ℕ → M)) = DRS.toRel proper := by
  ext ⟨a, a'⟩
  simp [DRS.toRel_iff, improper, proper, talks, Box.Extends]
  exact fun _ _ g _ hg ↦ ⟨g, fun _ ↦ rfl, hg⟩

end Representational

/-! ### fn. 4: the total-assignment semantics and re-declared referents

[muskens-1996]'s fn. 4 scopes the agreement of his semantics with standard DRT to total
assignments and notes a second difference: on `[ | [x | man x] ⇒ [x | mortal x]]`, where `x` is
declared twice, standard DRT ignores the second declaration and says that every man is mortal,
while here the second `x` takes a new value and the box says that there is a mortal if there is
a man. The partial semantics `DRS.Verifies` (`DRS/Verification.lean`) renders standard DRT: the
re-declaration is inert, and in a model with a non-mortal man the two truth values differ
(`fn4_diverges`). The witness is proper (`fn4_isProper`), so what fails is reuse-freeness
(`fn4_not_reuseFreeAt`), the hypothesis of the reconciliation
`DRS.trueRel_iff_exists_verifies`. -/

section Fn4

open FirstOrder FirstOrder.Language DRT

/-- The relation symbols of the fn. 4 witness are `man` and `mortal`. -/
inductive Fn4Rel : ℕ → Type
  | man : Fn4Rel 1
  | mortal : Fn4Rel 1

/-- The language of the fn. 4 witness (no function symbols). -/
def fn4Lang : Language := ⟨fun _ ↦ Empty, Fn4Rel⟩

/-- The antecedent `[x | man x]`. -/
def fn4Ante : DRS fn4Lang ℕ := .mk {0} [.atom ⟨.man, ![0]⟩]

/-- The consequent `[x | mortal x]`, re-declaring `x`. -/
def fn4Cons : DRS fn4Lang ℕ := .mk {0} [.atom ⟨.mortal, ![0]⟩]

/-- `[ | [x | man x] ⇒ [x | mortal x]]`, with the referent `0` declared twice. -/
def fn4 : DRS fn4Lang ℕ := .mk ∅ [.imp fn4Ante fn4Cons]

/-- A man (`0`) who is not mortal, and a mortal (`1`). -/
instance : fn4Lang.Structure (Fin 2) where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .man => fun args ↦ args 0 = 0
    | 1, .mortal => fun args ↦ args 0 = 1

theorem fn4_isProper : fn4.IsProper := by decide

theorem fn4_not_reuseFreeAt : ¬ DRS.ReuseFreeAt ∅ fn4 := by decide

theorem fn4_trueRel (g : ℕ → Fin 2) : DRS.trueRel fn4 g := by
  refine (DRS.trueRel_iff_exists_extends _ _).2 ⟨g, fun _ _ ↦ rfl, ?_⟩
  rw [verifiesTotal_iff]
  intro c hc
  simp only [fn4, DRS.conditions_mk, List.mem_singleton] at hc
  subst hc
  rw [verifiesTotal_imp]
  intro g₁ _ _
  refine ⟨Function.update g₁ 0 1,
    fun x hx ↦ by rw [Function.update_apply, ite_eq_right (by simpa [fn4Cons] using hx)], ?_⟩
  rw [verifiesTotal_iff]
  intro c hc
  simp only [fn4Cons, DRS.conditions_mk, List.mem_singleton] at hc
  subst hc
  rw [verifiesTotal_atom, Language.Atom.realize_mk]
  show Function.update g₁ 0 1 0 = 1
  simp

theorem fn4_not_isTrue : ¬ fn4.IsTrue (Fin 2) := by
  rintro ⟨g', -, hdom, himp, -⟩
  have hg' : g' = ⊥ :=
    PartialAssign.eq_of_le_of_domain_subset bot_le (by rw [hdom]; simp)
  subst hg'
  have hman : fn4Ante.Verifies (⊥ : PartialAssign ℕ (Fin 2)) (PartialAssign.single 0 0) := by
    rw [fn4Ante, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true, Condition.holds_atom]
    exact ⟨bot_le, by simp, ![0], fun i => by rw [Subsingleton.elim i 0]; simp, rfl⟩
  obtain ⟨g₂, hle₂, hdom₂, hmortal, -⟩ := himp _ hman
  have hg₂ : g₂ = PartialAssign.single 0 0 :=
    PartialAssign.eq_of_le_of_domain_subset hle₂ (by rw [hdom₂]; simp)
  obtain ⟨v, hv, hrel⟩ := hmortal
  have h0 : g₂ 0 = ↑(v 0) := hv 0
  rw [hg₂, PartialAssign.single_eq_same] at h0
  have hv0 : (0 : Fin 2) = v 0 := Flat.coe_injective h0
  have h1 : v 0 = 1 := hrel
  rw [← hv0] at h1
  exact absurd h1 (by decide)

/-- The reconciliation `DRS.trueRel_iff_exists_verifies` fails on the witness. -/
theorem fn4_diverges (g : ℕ → Fin 2) :
    ¬ (DRS.trueRel fn4 g ↔ fn4.IsTrue (Fin 2)) :=
  fun h ↦ fn4_not_isTrue (h.mp (fn4_trueRel g))

end Fn4

end Muskens1996
