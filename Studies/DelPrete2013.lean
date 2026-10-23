module

public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Mereology

/-!
# Del Prete (2013): Imperfectivity and habituality in Italian

This file formalizes the plurality-based analysis of the Italian Imperfetto in [del-prete-2013].
A bare imperfective is habitual or progressive according to whether its reference situation is
large or small, and on the habitual reading a singular indefinite object is understood as the
same object across the repeated events, the same-object effect of (2). The imperfective feature
spreads an event property over the forward expansion of the reference situation in a branching
model of situations, (16): every branch of the expanded situation lies within the temporal trace
of some event with the property. Verbs refer to plural events, [kratzer-2008]'s lexical
cumulativity hypothesis, and thematic roles are sum homomorphisms from events into the lattice
of individuals of [link-1983] and [krifka-1998], so a plural event whose theme is a singular
individual has that individual as the theme of each of its singular sub-events, the sameness
principle SSP. The same-object effect is thereby an entailment of the truth conditions (24), and
over a large reference situation the covering event must be plural, §5. A bare plural names the
kind, [carlson-1977] and [chierchia-1998], and a predication of a kind distributes its instances
over the singular sub-events, (21), so bare plurals show a kind-level effect only, (30); the
Q-adverb *sempre* forms a restricted universal over situations below the imperfective, (29), and
the indefinite in its scope varies with the situation. The oddness of (2b) against (2a) is then
[magri-2009]'s principle (O), §7: habitually reading one philosophy book conflicts with common
knowledge, habitually driving one sports car does not. Against the covert quantifier GEN of
[krifka-etal-1995], §2, the obligatory wide scope of indefinites that the effect would demand
gives the negated kind indefinite of (9b) the truth conditions (10b), strictly weaker than the
intuitive (10'b), whatever the appropriate situations GEN quantifies over
(`genWide_of_genNarrow`, `not_genNarrow_of_genWide`).

## Implementation notes

Tense and the reference time adverbial, (15) and (18), fix the reference situation, which
matters to the analysis only through its size, so the theorems are stated at the level of the
aspectual phrase, (24e). The branches of a situation are its sub-situations lying within a
single history, given by a predicate `linear`, and the forward expansion, taken from [deo-2009]
and which the chapter does not take to be a function, is a parameter `fexp` chosen per
utterance. Verbs are event predicates with the agent conjunct folded in, the lexical
cumulativity hypothesis is `Mereology.AlgClosure` of the singular events, and a plural event is
`Mereology.IsPlural`, the iteration of the same volume's [boneh-doron-2013]. The kind of a noun
is a parameter, the sum of its individuals, and a "kind coerced" indefinite ranges over a given
set of sub-kinds, parts of the kind. Example numbers are those of the HAL preprint hal-00920848.

## TODO

Footnote 28 argues that the sports car of (22) cannot vary across the branches of the expanded
situation, since the reference situation itself lies within the trace of each covering event.
The truth conditions (24g) choose a covering event per branch, and no axiom of the model
identifies the parts of two such events at the reference situation, so the sameness proved in
`hab_soe` is per covering event.

## References

* [del-prete-2013]
* [kratzer-2008]
* [link-1983]
* [krifka-1998]
* [carlson-1977]
* [chierchia-1998]
* [magri-2009]
* [krifka-etal-1995]
* [boneh-doron-2013]
* [deo-2009]
-/

@[expose] public section

namespace DelPrete2013

open Mereology

variable {S E I : Type*}

/-- `x` is an atomic part of `y`, the chapter's `x AT y`. -/
def AtomicPart {α : Type*} [PartialOrder α] (x y : α) : Prop := Atom x ∧ x ≤ y

/-! ### Throughout and the imperfective, §4.1 -/

section Aspect

variable [SemilatticeSup S] [SemilatticeSup E] (linear : S → Prop) (τ : SupHom E S)

/-- A branch of a situation: a sub-situation lying within a single history. -/
def Branch (b s : S) : Prop := linear b ∧ b ≤ s

/-- (16a) `THR`: `P` holds throughout `s` when every branch of `s` lies within the trace of a
`P`-event. -/
def THR (P : E → Prop) (s : S) : Prop := ∀ b, Branch linear b s → ∃ e, P e ∧ b ≤ τ e

/-- (16b) `IMPF`: `P` holds throughout the forward expansion of the reference situation. -/
def IMPF (fexp : S → S) (P : E → Prop) (s : S) : Prop := THR linear τ P (fexp s)

/-- A situation is large for `V₀`-events when no singular `V₀`-event's trace covers a branch
of it, the size that forces a plural covering event, §5. -/
def Large (V₀ : E → Prop) (s : S) : Prop := ∀ b, Branch linear b s → ∀ e, V₀ e → ¬ b ≤ τ e

variable {linear τ}

/-- HAB, §5: over a large situation, a covering event of a cumulative verb is plural. -/
theorem isPlural_of_large {V₀ : E → Prop} (hV₀ : ∀ ⦃e⦄, V₀ e → Atom e) {s : S}
    (hL : Large linear τ V₀ s) {b : S} (hb : Branch linear b s) {e : E}
    (he : AlgClosure V₀ e) (hbe : b ≤ τ e) : IsPlural V₀ e :=
  (isPlural_iff_of_atom hV₀).2 ⟨he, λ ha => hL b hb e (of_algClosure_of_atom he ha) hbe⟩

/-- PROG, §5: over a small reference situation, a single singular event whose trace covers the
expanded situation verifies the same denotation. -/
theorem impf_of_le {V₀ : E → Prop} {fexp : S → S} {s : S} {e : E} (he : V₀ e)
    (hs : fexp s ≤ τ e) : IMPF linear τ fexp (AlgClosure V₀) s :=
  λ _ hb => ⟨e, .base he, hb.2.trans hs⟩

end Aspect

/-! ### Singular indefinites, bare plurals and Q-adverbs, §4.3 -/

section Objects

variable [SemilatticeSup E] [SemilatticeSup I] (Th : SupHom E I)

/-- (24d): a verb with a singular indefinite object, `λe. ∃x [N(x) ∧ V(e) ∧ Th(e) = x]`. -/
def indefinite (N : I → Prop) (V : E → Prop) (e : E) : Prop := ∃ x, N x ∧ V e ∧ Th e = x

/-- (21) Distribution to Sub-Events: a predication of a plural event and a kind distributes
instances of the kind over the singular sub-events. -/
def distributes (P : E → I → Prop) (e : E) (k : I) : Prop :=
  ∀ e', AtomicPart e' e → ∃ x, AtomicPart x k ∧ P e' x

/-- (30''a): a verb with a bare plural object names the kind `k` of the noun, and the
predication distributes by (21). -/
def barePlural (V : E → Prop) (k : I) (e : E) : Prop :=
  distributes (λ e x => V e ∧ Th e = x) e k

/-- (27a,b): a "kind coerced" singular indefinite quantifies over the sub-kinds `K` of the
noun's kind, and the predication of the sub-kind distributes by (21). -/
def kindIndefinite (K : I → Prop) (V : E → Prop) (e : E) : Prop :=
  ∃ X, K X ∧ barePlural Th V X e

/-- (29''b) `[sempre C]`: for every situation with the contextual property `C`, an event with
the property `P` in the contextual temporal relation `R` to it is part of the event described. -/
def sempre (C : S → Prop) (R : E → S → Prop) (P : E → Prop) (e₀ : E) : Prop :=
  ∀ s₁, C s₁ → ∃ e₁, P e₁ ∧ R e₁ s₁ ∧ e₁ ≤ e₀

variable {Th}

section SSP

variable (hTh : ∀ e, Atom e → ¬ IsBot (Th e))
include hTh

theorem ssp {x : I} (hx : Atom x) {e e' : E} (h : Th e = x) (he' : AtomicPart e' e) :
    Th e' = x :=
  hx.eq (h ▸ OrderHomClass.monotone Th he'.2) (hTh e' he'.1)

/-- The same-object effect, §5: an event of (24d) has one `N`-individual as the theme of each
of its singular sub-events. -/
theorem soe {N : I → Prop} (hN : ∀ ⦃x⦄, N x → Atom x) {V : E → Prop} {e : E}
    (h : indefinite Th N V e) : ∃ x, N x ∧ ∀ e', AtomicPart e' e → Th e' = x :=
  let ⟨x, hx, _, h'⟩ := h; ⟨x, hx, λ _ he' => ssp hTh (hN hx) h' he'⟩

end SSP

/-- (9a) entails (13), §3: a kind coerced indefinite over sub-kinds of the kind entails the
bare plural. -/
theorem barePlural_of_kindIndefinite {K : I → Prop} {k : I} (hK : ∀ ⦃X⦄, K X → X ≤ k)
    {V : E → Prop} {e : E} (h : kindIndefinite Th K V e) : barePlural Th V k e :=
  let ⟨_, hX, hd⟩ := h
  λ e' he' => let ⟨x, ⟨hx, hxX⟩, hP⟩ := hd e' he'; ⟨x, ⟨hx, hxX.trans (hK hX)⟩, hP⟩

/-- (13) does not entail (9a), footnote 12: Gianni smokes a Toscanello and a Mori, and no
sub-kind of tuscan cigar is the kind he smokes. -/
theorem not_kindIndefinite_of_barePlural :
    ∃ (E I : Type) (_ : SemilatticeSup E) (_ : SemilatticeSup I) (Th : SupHom E I)
      (K : I → Prop) (k : I) (V : E → Prop) (e : E),
      (∀ ⦃X⦄, K X → X ≤ k) ∧ barePlural Th V k e ∧ ¬ kindIndefinite Th K V e :=
  ⟨Finset (Fin 2), Finset (Fin 2), inferInstance, inferInstance, SupHom.id _,
    λ X => X = {0} ∨ X = {1}, {0, 1}, λ _ => True, {0, 1}, by decide,
    by unfold barePlural distributes AtomicPart; decide,
    by unfold kindIndefinite barePlural distributes AtomicPart; decide⟩

theorem sempre_of_forall_not {C : S → Prop} (hC : ∀ s, ¬ C s) (R : E → S → Prop)
    (P : E → Prop) (e₀ : E) : sempre C R P e₀ :=
  λ s hs => absurd hs (hC s)

/-- (29) has no same-object effect, §6: with the indefinite in the scope of `sempre`, the books
read on two occasions differ. -/
theorem sempre_indefinite_no_soe :
    ∃ (S E I : Type) (_ : SemilatticeSup E) (_ : SemilatticeSup I) (Th : SupHom E I)
      (C : S → Prop) (R : E → S → Prop) (N : I → Prop) (V : E → Prop) (e₀ : E),
      sempre C R (indefinite Th N V) e₀ ∧ ¬ ∃ x, ∀ e', AtomicPart e' e₀ → Th e' = x :=
  ⟨Fin 2, Finset (Fin 2), Finset (Fin 2), inferInstance, inferInstance, SupHom.id _,
    λ _ => True, λ e s => e = {s}, λ x => x = {0} ∨ x = {1}, λ _ => True, {0, 1},
    by unfold sempre indefinite; decide, by unfold AtomicPart; decide⟩

/-- (30) has no same-object effect, §6: the bare plural distributes, and two singular readings
have different books as themes. -/
theorem barePlural_no_soe :
    ∃ (E I : Type) (_ : SemilatticeSup E) (_ : SemilatticeSup I) (Th : SupHom E I)
      (V : E → Prop) (k : I) (e : E),
      barePlural Th V k e ∧ ¬ ∃ x, ∀ e', AtomicPart e' e → Th e' = x :=
  ⟨Finset (Fin 2), Finset (Fin 2), inferInstance, inferInstance, SupHom.id _, λ _ => True,
    {0, 1}, {0, 1}, by unfold barePlural distributes AtomicPart; decide,
    by unfold AtomicPart; decide⟩

end Objects

/-! ### The same-object effect and its oddness, §5 and §7 -/

section SameObject

variable [SemilatticeSup S] [SemilatticeSup E] [SemilatticeSup I] {linear : S → Prop}
  {τ : SupHom E S} {Th : SupHom E I} (hTh : ∀ e, Atom e → ¬ IsBot (Th e))
include hTh

/-- (P1), §5: on the habitual reading, every branch of the large expanded situation is covered
by a plural `V₀`-event, and one `N`-individual is the theme of each of its singular sub-events. -/
theorem hab_soe {V₀ : E → Prop} (hV₀ : ∀ ⦃e⦄, V₀ e → Atom e) {N : I → Prop}
    (hN : ∀ ⦃x⦄, N x → Atom x) {fexp : S → S} {s : S} (hL : Large linear τ V₀ (fexp s))
    (h : IMPF linear τ fexp (indefinite Th N (AlgClosure V₀)) s) {b : S}
    (hb : Branch linear b (fexp s)) :
    ∃ e, IsPlural V₀ e ∧ b ≤ τ e ∧ ∃ x, N x ∧ ∀ e', AtomicPart e' e → Th e' = x :=
  let ⟨e, ⟨x, hx, hcl, h'⟩, hbe⟩ := h b hb
  ⟨e, isPlural_of_large hV₀ hL hb hcl hbe, hbe, x, hx, λ _ he' => ssp hTh (hN hx) h' he'⟩

/-- (2b) is odd on HAB by principle (O), §7: it is common knowledge that a habit of reading
philosophy books involves different books, and the habitual truth conditions entail a plural
reading event of one book throughout. -/
theorem not_impf_indefinite {read₀ : E → Prop} (hV₀ : ∀ ⦃e⦄, read₀ e → Atom e)
    {book : I → Prop} (hN : ∀ ⦃x⦄, book x → Atom x)
    (hCK : ∀ e, IsPlural read₀ e → ∀ x, book x → ∃ e', AtomicPart e' e ∧ Th e' ≠ x)
    {fexp : S → S} {s : S} (hL : Large linear τ read₀ (fexp s)) {b : S}
    (hb : Branch linear b (fexp s)) :
    ¬ IMPF linear τ fexp (indefinite Th book (AlgClosure read₀)) s := by
  intro h
  obtain ⟨e, hpl, -, x, hx, hsame⟩ := hab_soe hTh hV₀ hN hL h hb
  obtain ⟨e', he', hne⟩ := hCK e hpl x hx
  exact hne (hsame e' he')

end SameObject

/-- (2a) is good on HAB, §7: a plural event of driving one sports car covers the large expanded
situation, and no common knowledge excludes it. -/
theorem impf_indefinite_witness :
    ∃ (S E I : Type) (_ : SemilatticeSup S) (_ : SemilatticeSup E) (_ : SemilatticeSup I)
      (linear : S → Prop) (τ : SupHom E S) (Th : SupHom E I) (drive₀ : E → Prop)
      (car : I → Prop) (fexp : S → S) (s : S),
      (∀ ⦃e⦄, drive₀ e → Atom e) ∧ (∀ ⦃x⦄, car x → Atom x) ∧ (∀ e, Atom e → ¬ IsBot (Th e)) ∧
        Large linear τ drive₀ (fexp s) ∧ (∃ b, Branch linear b (fexp s)) ∧
        IMPF linear τ fexp (indefinite Th car (AlgClosure drive₀)) s :=
  ⟨Finset (Fin 2), Finset (Fin 2), Finset (Fin 1), inferInstance, inferInstance, inferInstance,
    (· = {0, 1}), SupHom.id _, SupHom.const _ {0}, λ e => e = {0} ∨ e = {1}, (· = {0}),
    λ _ => {0, 1}, {0}, by decide, by decide, by decide, by unfold Large Branch; decide,
    ⟨{0, 1}, rfl, le_rfl⟩, by
      rintro b ⟨rfl, -⟩
      exact ⟨{0} ⊔ {1}, ⟨{0}, rfl, .sum (.base (Or.inl rfl)) (.base (Or.inr rfl)), rfl⟩,
        by decide⟩⟩

/-! ### Against the covert quantifier, §2

GEN quantifies over the appropriate situations of its restrictor, which a normality on
situations selects. -/

section Gen

open Genericity

variable (N : Normality Unit S) (K : I → Prop) (φ : S → Prop) (P : I → S → Prop)

/-- (10b): the negated kind indefinite of (9b) scoping over GEN, as assumption (α)1 demands:
there is no sub-kind of tuscan cigar that Gianni smokes in every appropriate situation. -/
def genWide : Prop := ¬ ∃ X, K X ∧ () ∈ N.gen {s | φ s} {s | P X s}

/-- (10'b): the negation below GEN: in no appropriate situation does Gianni smoke a sub-kind of
tuscan cigar. -/
def genNarrow : Prop := () ∈ N.gen {s | φ s} {s | ¬ ∃ X, K X ∧ P X s}

variable {N K φ P}

/-- (10'b) is logically stronger than (10b), whatever the appropriate situations, provided there
is one. -/
theorem genWide_of_genNarrow (hφ : (N.normal () {s | φ s}).Nonempty) (h : genNarrow N K φ P) :
    genWide N K φ P :=
  fun ⟨X, hX, hall⟩ ↦ let ⟨_, hs⟩ := hφ; h hs ⟨X, hX, hall hs⟩

/-- (10b) is too weak: where every situation is appropriate and Gianni smokes a tuscan cigar of
one sub-kind or another in each, (10b) holds while (9b) is false, as (10'b) is. -/
theorem not_genNarrow_of_genWide :
    ∃ (S I : Type) (N : Normality Unit S) (K : I → Prop) (φ : S → Prop) (P : I → S → Prop),
      (N.normal () {s | φ s}).Nonempty ∧ genWide N K φ P ∧ ¬ genNarrow N K φ P :=
  ⟨Bool, Bool, ⊤, fun _ ↦ True, fun _ ↦ True, (· = ·), ⟨true, trivial⟩,
    fun ⟨X, _, hall⟩ ↦ absurd (hall (show (!X) ∈ {_s : Bool | True} from trivial))
      (by cases X <;> decide),
    fun h ↦ h (show true ∈ {_s : Bool | True} from trivial) ⟨true, trivial, rfl⟩⟩

end Gen

end DelPrete2013
