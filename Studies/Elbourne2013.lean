module

public import Linglib.Data.Examples.Elbourne2013
public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Presupposition.Basic
public import Mathlib.Order.Minimal

/-!
# Elbourne (2013): Definite Descriptions

Elbourne gives the definite article a Fregean semantics over situations, the parts of possible
worlds ordered by parthood. The article takes a property and a situation and, if exactly one
thing has the property there, denotes that thing, so a description is a partial function from
situations to individuals. Its situation pronoun is free, referring to a situation the context
supplies, or bound by the abstractor of the containing proposition: free pronouns give Donnellan's
referential use and bound ones the attributive use. Binding the pronoun below an intensional
operator gives the de dicto reading, letting it refer to the actual world the de re reading, and
binding it above the operator Kripke's attributive yet de re reading. Under an attitude verb the
presupposition projects to the subject's beliefs, after Karttunen, and a donkey-anaphoric
description is bound to the minimal situations of its restrictor, which gives donkey sentences
their strong reading and a repeated description no sloppy reading.

## Main definitions

* `the`, `description`, `sentence`: the article, a description with its situation pronoun, and a
  sentence as a trivalent proposition.
* `deDicto`, `deRe`, `attributiveDeRe`, `attitude`: descriptions under intensional operators and
  attitude verbs.
* `Village`: situations as finite sets of atomic facts.

## Main results

* `sentence_ne_zero_iff`: a sentence presupposes exactly one satisfier at the situation its
  pronoun denotes.
* `deDicto_ne_zero_iff`, `deRe_ne_zero_iff`, `attributiveDeRe_eq_one_iff`: the three readings
  under an intensional operator.
* `attitude_eq_zero_of_agnostic`, `russellian_consistent`: the description, unlike its
  Russellian paraphrase, makes an agnostic subject's desire infelicitous.
* `everyOwnerBeatsTheDonkey_iff`, `incomplete_description`,
  `everyOwnerBeatsTheDonkeyAndThePriestToo_iff`: the strong donkey reading, incompleteness, and
  the strict reading of a repeated description in the village.

## Implementation notes

* Situations are any partial order; minimality is mathlib's `Minimal`, and the lexical entries of
  §2.3.3 are transcribed with it. The article is `iota` at the situation, so its domain
  condition is `∃!` (`the_isSome_iff`), and a sentence is `Presupposition.presupOfReferent` of
  the description. A situation pronoun is its value as a function of the situation the
  proposition is applied to, constant when free and the identity when bound. A description
  inside a scope contributes `∃ z ∈ the f s`, the condition under which `presupOfReferent` is
  true, with `Option` membership.
* Intensional operators are universal over an accessibility relation and lift trivalent
  propositions by the Weak Kleene universal over the accessible situations
  (`Trivalent.forallWeak`); attitude verbs are defined where the complement is defined
  throughout the subject's doxastic alternatives and true where it is true throughout the
  verb's own, Karttunen's projection.
* The village of ch. 6 and ch. 9 is a concrete model: situations are finite sets of atomic
  facts ordered by inclusion, Kratzer's states of affairs, so minimal situations are
  computed and the strong reading of the donkey sentence is a theorem rather than a reading of
  the truth conditions.
* The examples are `Data.Examples.Elbourne2013`. The ch. 8 contrast rows and the ch. 9
  sloppy-identity rows are read by `contrast_rows` and `sloppy_rows`; the remaining rows record
  the readings and analyses the theorems above derive.

## TODO

* Ch. 4's projection through possibility modals, disjunction and negation, ch. 7's modal
  subordination and counterfactuals, and ch. 10's descriptive indexicals are not represented.

## References

* [elbourne-2013]
* [elbourne-2005]
* [kratzer-1989]
* [barwise-perry-1983]
* [heim-kratzer-1998]
* [buring-2004]
* [strawson-1950]
* [russell-1905]
* [donnellan-1966]
* [kripke-1977]
* [karttunen-1974-presupposition]
* [stanley-szabo-2000]
* [geach-1962]
-/

@[expose] public section

namespace Elbourne2013

open Presupposition

/-! ### Quantification over minimal situations (§2.3.3) -/

section Quantification

variable {S : Type*} [PartialOrder S] {E : Type*}

/-- The morpheme `Q`, (22), holds of `x` when there is an extended situation, a minimal situation
between `s'` and `s` in which `x` has the property. -/
def Q (f : E → S → Prop) (x : E) (s s' : S) : Prop :=
  ∃ s'', Minimal (fun s'' ↦ s' ≤ s'' ∧ s'' ≤ s ∧ f x s'') s''

/-- `every`, (20), holds when every minimal situation, within the restrictor situation `s₀` and
the truth-supporting situation `s`, in which an individual has the restrictor property satisfies
the nuclear scope. -/
def every (s₀ : S) (f : E → S → Prop) (g : E → S → S → Prop) (s : S) : Prop :=
  ∀ x s', Minimal (fun s' ↦ s' ≤ s₀ ∧ s' ≤ s ∧ f x s') s' → g x s s'

/-- `a`, (21), holds when some minimal restrictor situation satisfies the nuclear scope. -/
def a (s₀ : S) (f : E → S → Prop) (g : E → S → S → Prop) (s : S) : Prop :=
  ∃ x s', Minimal (fun s' ↦ s' ≤ s₀ ∧ s' ≤ s ∧ f x s') s' ∧ g x s s'

/-- `always`, (33), holds when every minimal situation in `s` satisfying the antecedent satisfies
the consequent. -/
def always (p : S → Prop) (q : S → S → Prop) (s : S) : Prop :=
  ∀ s', Minimal (fun s' ↦ s' ≤ s ∧ p s') s' → q s s'

/-- The morpheme `Q_A`, (34), is the propositional counterpart of `Q`. -/
def QA (p : S → Prop) (s s' : S) : Prop :=
  ∃ s'', Minimal (fun s'' ↦ s' ≤ s'' ∧ s'' ≤ s ∧ p s'') s''

end Quantification

/-! ### The article and its situation pronoun (ch. 3–5) -/

section Article

variable {S E : Type*}

/-- The definite article, (3) of ch. 3, is `λf.λs : ∃!x f(x)(s). ιx f(x)(s)`, a partial function
from situations to the unique satisfier of the property in the situation. -/
noncomputable def the (f : E → S → Prop) (s : S) : Option E := iota (f · s)

theorem the_isSome_iff (f : E → S → Prop) (s : S) : (the f s).isSome ↔ ∃! x, f x s :=
  iota_isSome_iff _

theorem the_eq_some_iff (f : E → S → Prop) (s : S) (x : E) :
    the f s = some x ↔ f x s ∧ ∀ y, f y s → y = x :=
  iota_eq_some_iff _

/-- A pronoun, (4b) of ch. 10, has the article's entry, its noun phrase supplied by
NP-deletion. -/
noncomputable def pronoun (np : E → S → Prop) : S → Option E := the np

/-- `[[the NP] sᵢ]`, (4) of ch. 3, is the description with its situation pronoun, whose value is
the function `σ` of the situation the containing proposition is applied to. A free pronoun is
constant, so that the referent enters via the context and is the same wherever the proposition
is applied, the referential use of (11) of ch. 5; a bound one is the identity (Situation Binding
I and λ-Conversion II), so that the individual described depends on the situation of
evaluation, the attributive use of (15) of ch. 5. -/
noncomputable def description (σ : S → S) (f : E → S → Prop) (s : S) : Option E :=
  the f (σ s)

/-- `[[[the NP] sᵢ] VP]` is the sentence as a trivalent proposition, (3) of ch. 4 for a free
pronoun and (4) for a bound one. -/
noncomputable def sentence (σ : S → S) (f vp : E → S → Prop) : S → SignType :=
  presupOfReferent (description σ f) vp

/-- The sentence presupposes exactly one satisfier at the situation its pronoun denotes. A free
pronoun discharges the domain condition at its referent, whatever situation the proposition is
applied to; a bound one carries it to the situation where the proposition is applied. -/
theorem sentence_ne_zero_iff (σ : S → S) (f vp : E → S → Prop) (s : S) :
    sentence σ f vp s ≠ 0 ↔ ∃! x, f x (σ s) := by
  rw [sentence, Ne, presupOfReferent_eq_zero_iff, ← Ne, Option.ne_none_iff_isSome]
  exact the_isSome_iff f (σ s)

/-- Where the description denotes an individual, the sentence says the predicate of that individual
((12) of ch. 5). -/
theorem sentence_eq_one_iff (σ : S → S) (f vp : E → S → Prop) {s : S} {x : E}
    (h : description σ f s = some x) : sentence σ f vp s = 1 ↔ vp x s := by
  simp [sentence, presupOfReferent_of_some h]

/-! ### Intensional operators: de re, de dicto, attributive de re (ch. 7) -/

/-- A universal intensional operator over an accessibility relation is the Weak Kleene universal
over the accessible situations, defined where the proposition is defined throughout them and true
where it is true throughout them, as in (12) and (14) of ch. 7. -/
noncomputable def box (R : S → Set S) (p : S → SignType) : S → SignType :=
  fun s ↦ Trivalent.forallWeak fun w : R s ↦ p w

theorem box_ne_zero_iff (R : S → Set S) (p : S → SignType) (s : S) :
    box R p s ≠ 0 ↔ ∀ w ∈ R s, p w ≠ 0 := by
  simp [box]

/-- De dicto, (11) of ch. 7, the situation pronoun is bound by `ς` immediately below the
operator. -/
noncomputable def deDicto (R : S → Set S) (f vp : E → S → Prop) : S → SignType :=
  box R (sentence id f vp)

/-- De re, (13) of ch. 7, the situation pronoun inside the operator refers to the actual world
`w₀`. -/
noncomputable def deRe (R : S → Set S) (w₀ : S) (f vp : E → S → Prop) : S → SignType :=
  box R (sentence (fun _ ↦ w₀) f vp)

/-- Attributive de re, (17) and (25) of ch. 7, the pronoun is bound above the operator, so the
description is evaluated at the topic situation and only the predicate is modalized. -/
noncomputable def attributiveDeRe (R : S → Set S) (f vp : E → S → Prop) : S → SignType :=
  presupOfReferent (the f) fun x s ↦ ∀ w ∈ R s, vp x w

/-- De dicto, every accessible situation must contain exactly one satisfier, and the satisfiers
may differ. -/
theorem deDicto_ne_zero_iff (R : S → Set S) (f vp : E → S → Prop) (s : S) :
    deDicto R f vp s ≠ 0 ↔ ∀ w ∈ R s, ∃! x, f x w :=
  (box_ne_zero_iff R _ s).trans <| forall₂_congr fun w _ ↦ sentence_ne_zero_iff id f vp w

/-- De re, the satisfier is fixed in the actual world, and need not satisfy the property in the
accessible situations. -/
theorem deRe_ne_zero_iff (R : S → Set S) (w₀ : S) (f vp : E → S → Prop) (s : S) :
    deRe R w₀ f vp s ≠ 0 ↔ ∀ w ∈ R s, ∃! x, f x w₀ :=
  (box_ne_zero_iff R _ s).trans <| forall₂_congr fun w _ ↦
    sentence_ne_zero_iff (fun _ ↦ w₀) f vp w

theorem attributiveDeRe_ne_zero_iff (R : S → Set S) (f vp : E → S → Prop) (s : S) :
    attributiveDeRe R f vp s ≠ 0 ↔ ∃! x, f x s :=
  sentence_ne_zero_iff id f _ s

/-- Kripke's *the number of the planets* is attributive yet de re ((16) of ch. 7). -/
theorem attributiveDeRe_eq_one_iff (R : S → Set S) (f vp : E → S → Prop) {s : S} {x : E}
    (h : the f s = some x) : attributiveDeRe R f vp s = 1 ↔ ∀ w ∈ R s, vp x w :=
  sentence_eq_one_iff id f _ h

/-! ### Existence entailments (ch. 8) -/

open Classical in
/-- An attitude verb with [karttunen-1974-presupposition]'s projection (§8.6) is defined where the
complement is defined throughout the subject's doxastic alternatives, and true where the
complement is true throughout the verb's own alternatives, doxastic for *believe* and bouletic for
*want*. -/
noncomputable def attitude (dox R : S → Set S) (p : S → SignType) : S → SignType :=
  {s | ∀ w ∈ dox s, p w ≠ 0}.indicator fun s ↦ SignType.ofProp (∀ w ∈ R s, p w = 1)

/-- *Hans wants the ghost in his attic to be quiet* presupposes Hans's belief in exactly one such
ghost ((40)–(41) of ch. 8). -/
theorem attitude_ne_zero_iff (dox R : S → Set S) (f vp : E → S → Prop) (s : S) :
    attitude dox R (sentence id f vp) s ≠ 0 ↔ ∀ w ∈ dox s, ∃! x, f x w := by
  simp only [attitude, ne_eq, Set.indicator_apply_eq_zero, Set.mem_ofPred_eq,
    SignType.ofProp_ne_zero, imp_false, not_not]
  exact forall₂_congr fun w _ ↦ sentence_ne_zero_iff id f vp w

/-- A subject unsure whether there is a ghost in his attic cannot felicitously want the ghost to be
quiet ((31) with (33b)). -/
theorem attitude_eq_zero_of_agnostic (dox R : S → Set S) (f vp : E → S → Prop) {s : S}
    (h : ∃ w ∈ dox s, ¬ ∃ x, f x w) : attitude dox R (sentence id f vp) s = 0 := by
  refine not_not.1 fun hp ↦ ?_
  obtain ⟨w, hw, hno⟩ := h
  exact hno ((attitude_ne_zero_iff dox R f vp s).1 hp w hw).exists

/-- The Russellian paraphrase (33a) asserts existence and uniqueness inside the attitude. -/
def russellian (R : S → Set S) (f vp : E → S → Prop) (s : S) : Prop :=
  ∀ w ∈ R s, ∃ x, f x w ∧ (∀ y, f y w → y = x) ∧ vp x w

/-- The existence presupposition of a description in a conditional antecedent projects to the whole
conditional ((39) of ch. 8). -/
theorem conditional_ne_zero_iff (f vp : E → S → Prop) (q : S → SignType) (s : S) :
    (-sentence id f vp s).joinWeak (q s) ≠ 0 ↔ (∃! x, f x s) ∧ q s ≠ 0 := by
  rw [Ne, SignType.joinWeak_eq_zero_iff, SignType.neg_eq_zero_iff, not_or, ← Ne,
    sentence_ne_zero_iff]
  rfl

end Article

/-- The Russellian paraphrase is consistent with agnosticism about the ghost ((31) with (33a)). -/
theorem russellian_consistent :
    ∃ (dox R : Bool → Set Bool) (f vp : Unit → Bool → Prop),
      (∃ w ∈ dox true, ¬ ∃ x, f x w) ∧ russellian R f vp true :=
  ⟨fun _ ↦ Set.univ, fun _ ↦ {true}, fun _ w ↦ w = true, fun _ _ ↦ True,
    ⟨false, Set.mem_univ _, by simp⟩, fun w hw ↦ ⟨(), hw, fun _ _ ↦ rfl, trivial⟩⟩

/-- Under an attitude verb, the description presupposes a fountain of youth for the subject, not the
speaker ((36) of ch. 8). -/
theorem attitude_ne_zero_not_speaker :
    ∃ (dox R : Bool → Set Bool) (f vp : Unit → Bool → Prop) (s : Bool),
      attitude dox R (sentence id f vp) s ≠ 0 ∧ ¬ ∃ x, f x s :=
  ⟨fun _ ↦ {true}, fun _ ↦ {true}, fun _ w ↦ w = true, fun _ _ ↦ True, false,
    (attitude_ne_zero_iff _ _ _ _ _).mpr fun w hw ↦ ⟨(), hw, fun _ _ ↦ rfl⟩, by simp⟩

/-! ### The village: situations as sets of facts (ch. 6, ch. 9) -/

/-- The atomic facts of a village are [kratzer-1989]'s states of affairs, thin particulars
instantiating properties and relations. -/
inductive Fact (E : Type*)
  | farmer (x : E)
  | donkey (x : E)
  | priest (x : E)
  | table (x : E)
  | covered (x : E)
  | owns (x y : E)
  | beats (x y : E)
  deriving DecidableEq

/-- A situation is a finite set of facts, parthood is inclusion, and a world is the set of all
the facts that hold in it. -/
abbrev Village (E : Type*) := Finset (Fact E)

section Village

variable {E : Type*}

theorem exists_minimal_singleton_iff {t u : Village E} (φ : Fact E) (g : Village E → Prop) :
    (∃ s, Minimal (fun s ↦ s ≤ t ∧ s ≤ u ∧ φ ∈ s) s ∧ g s) ↔ φ ∈ t ∧ φ ∈ u ∧ g {φ} := by
  have hmin (ht : φ ∈ t) (hu : φ ∈ u) (s : Village E) :
      Minimal (fun s ↦ s ≤ t ∧ s ≤ u ∧ φ ∈ s) s ↔ s = {φ} :=
    minimal_iff_eq ⟨Finset.singleton_subset_iff.mpr ht, Finset.singleton_subset_iff.mpr hu,
      Finset.mem_singleton_self φ⟩ fun _ h ↦ Finset.singleton_subset_iff.mpr h.2.2
  constructor
  · rintro ⟨s, hs, hg⟩
    have ht := hs.prop.1 hs.prop.2.2
    have hu := hs.prop.2.1 hs.prop.2.2
    exact ⟨ht, hu, (hmin ht hu s).mp hs ▸ hg⟩
  · rintro ⟨ht, hu, hg⟩
    exact ⟨{φ}, (hmin ht hu _).mpr rfl, hg⟩

variable [DecidableEq E]

theorem Q_subset_iff (Φ : E → Village E) (x : E) (s s' : Village E) :
    Q (fun x s'' ↦ Φ x ⊆ s'') x s s' ↔ s' ≤ s ∧ Φ x ⊆ s := by
  constructor
  · rintro ⟨s'', hs''⟩
    exact ⟨hs''.prop.1.trans hs''.prop.2.1, hs''.prop.2.2.trans hs''.prop.2.1⟩
  · rintro ⟨hle, hsub⟩
    exact ⟨s' ∪ Φ x, (minimal_iff_eq ⟨Finset.subset_union_left, Finset.union_subset hle hsub,
      Finset.subset_union_right⟩ fun _ h ↦ Finset.union_subset h.1 h.2.2).mpr rfl⟩

theorem Q_mem_iff (φ : E → Fact E) (x : E) (s s' : Village E) :
    Q (fun x s'' ↦ φ x ∈ s'') x s s' ↔ s' ≤ s ∧ φ x ∈ s := by
  simpa only [Finset.singleton_subset_iff] using Q_subset_iff (fun x ↦ {φ x}) x s s'

/-- *man who owns a donkey* is the restrictor of (4) in ch. 6, with `a` and `Q` inside the
relative clause. -/
def ownsADonkey (s₀ : Village E) (x : E) (s' : Village E) : Prop :=
  Fact.farmer x ∈ s' ∧
    a s₀ (fun y (s : Village E) ↦ Fact.donkey y ∈ s)
      (fun y ↦ Q (fun y (s : Village E) ↦ Fact.owns x y ∈ s) y) s'

theorem ownsADonkey_iff (s₀ : Village E) (x : E) {s' : Village E} (h : s' ≤ s₀) :
    ownsADonkey s₀ x s' ↔ Fact.farmer x ∈ s' ∧ ∃ y, Fact.donkey y ∈ s' ∧ Fact.owns x y ∈ s' := by
  simp only [ownsADonkey, a, exists_minimal_singleton_iff, Q_mem_iff, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hf, y, -, hd, -, ho⟩
    exact ⟨hf, y, hd, ho⟩
  · rintro ⟨hf, y, hd, ho⟩
    exact ⟨hf, y, h hd, hd, hd, ho⟩

theorem minimal_ownsADonkey_iff (w : Village E) (x : E) (s' : Village E) :
    Minimal (fun s' ↦ s' ≤ w ∧ s' ≤ w ∧ ownsADonkey w x s') s' ↔
      ∃ y, Fact.farmer x ∈ w ∧ Fact.donkey y ∈ w ∧ Fact.owns x y ∈ w ∧
        s' = {Fact.farmer x, Fact.donkey y, Fact.owns x y} := by
  constructor
  · intro hs
    obtain ⟨hw, -, hr⟩ := hs.prop
    obtain ⟨hf, y, hd, ho⟩ := (ownsADonkey_iff w x hw).mp hr
    have hsub : ({Fact.farmer x, Fact.donkey y, Fact.owns x y} : Village E) ≤ s' := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hf, hd, ho⟩
    have hA : ({Fact.farmer x, Fact.donkey y, Fact.owns x y} : Village E) ≤ w := hsub.trans hw
    refine ⟨y, hw hf, hw hd, hw ho, hs.eq_of_ge ⟨hA, hA, ?_⟩ hsub⟩
    rw [ownsADonkey_iff w x hA]
    simp
  · rintro ⟨y, hf, hd, ho, rfl⟩
    have hA : ({Fact.farmer x, Fact.donkey y, Fact.owns x y} : Village E) ≤ w := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hf, hd, ho⟩
    refine ⟨⟨hA, hA, ?_⟩, ?_⟩
    · rw [ownsADonkey_iff w x hA]
      simp
    · intro s hs hle
      obtain ⟨hf', y', hd', ho'⟩ := (ownsADonkey_iff w x hs.1).mp hs.2.2
      have hy : y' = y := by
        have := hle hd'
        simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or, or_false,
          Fact.donkey.injEq] at this
        exact this
      subst hy
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hf', hd', ho'⟩

theorem the_donkey_minimal (x y : E) :
    the (fun z (s : Village E) ↦ Fact.donkey z ∈ s) {Fact.farmer x, Fact.donkey y, Fact.owns x y} =
      some y := by
  rw [the_eq_some_iff]
  refine ⟨by simp, fun z hz ↦ ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or, or_false,
    Fact.donkey.injEq] at hz
  exact hz

/-- Every minimal situation of a farmer owning a donkey contains exactly one donkey (§6.2). -/
theorem existsUnique_donkey_of_minimal (w : Village E) (x : E) {s' : Village E}
    (hs : Minimal (fun s' ↦ s' ≤ w ∧ s' ≤ w ∧ ownsADonkey w x s') s') :
    ∃! z, Fact.donkey z ∈ s' := by
  obtain ⟨y, -, -, -, rfl⟩ := (minimal_ownsADonkey_iff w x s').mp hs
  exact (the_isSome_iff (fun z (s : Village E) ↦ Fact.donkey z ∈ s) _).mp
    (by rw [the_donkey_minimal]; rfl)

/-- The nuclear scope of (4) in ch. 6 is `σ₃ [Q [beats [the donkey s₃]]]`. Situation Binding III
binds the description to the restrictor's minimal situation `s'`, and `Q` extends `s'` to a
situation in which the beating holds. -/
noncomputable def beatsTheDonkey (x : E) (s s' : Village E) : Prop :=
  Q (fun x s'' ↦ ∃ z ∈ the (fun z (s : Village E) ↦ Fact.donkey z ∈ s) s', Fact.beats x z ∈ s'')
    x s s'

/-- This is (3) of ch. 6, *every man who owns a donkey beats the donkey*, with the LF (4). -/
noncomputable def everyOwnerBeatsTheDonkey (s₀ s : Village E) : Prop :=
  every s₀ (ownsADonkey s₀) beatsTheDonkey s

/-- In (10a) of ch. 10, *every man who owns a donkey beats it*, the pronoun with its deleted noun
phrase stands in place of the description. -/
noncomputable def everyOwnerBeatsIt (s₀ s : Village E) : Prop :=
  every s₀ (ownsADonkey s₀)
    (fun x s s' ↦ Q (fun x s'' ↦ ∃ z ∈ pronoun (fun z (s : Village E) ↦ Fact.donkey z ∈ s) s',
      Fact.beats x z ∈ s'') x s s') s

private theorem beatsTheDonkey_iff (w : Village E) (x y : E) :
    beatsTheDonkey x w {Fact.farmer x, Fact.donkey y, Fact.owns x y} ↔
      {Fact.farmer x, Fact.donkey y, Fact.owns x y} ≤ w ∧ Fact.beats x y ∈ w := by
  unfold beatsTheDonkey
  rw [the_donkey_minimal]
  simp only [Option.mem_def, Option.some.injEq, exists_eq_left']
  exact Q_mem_iff (fun x ↦ Fact.beats x y) x w _

/-- On the neat semantics for donkey sentences (§6.2), the donkey sentence is true iff every farmer
beats every donkey he owns. -/
theorem everyOwnerBeatsTheDonkey_iff (w : Village E) :
    everyOwnerBeatsTheDonkey w w ↔
      ∀ x y, Fact.farmer x ∈ w → Fact.donkey y ∈ w → Fact.owns x y ∈ w → Fact.beats x y ∈ w := by
  constructor
  · intro h x y hf hd ho
    exact ((beatsTheDonkey_iff w x y).mp
      (h x _ ((minimal_ownsADonkey_iff w x _).mpr ⟨y, hf, hd, ho, rfl⟩))).2
  · intro h x s' hs
    obtain ⟨y, hf, hd, ho, rfl⟩ := (minimal_ownsADonkey_iff w x s').mp hs
    exact (beatsTheDonkey_iff w x y).mpr ⟨hs.prop.1, h x y hf hd ho⟩

theorem everyOwnerBeatsIt_iff (w : Village E) :
    everyOwnerBeatsIt w w ↔
      ∀ x y, Fact.farmer x ∈ w → Fact.donkey y ∈ w → Fact.owns x y ∈ w → Fact.beats x y ∈ w :=
  everyOwnerBeatsTheDonkey_iff w

end Village

/-! ### Incompleteness and the argument from sloppy identity (ch. 9) -/

/-- The room of (4) in ch. 9 has one table, covered with books. -/
def room : Village Bool := {Fact.table true, Fact.covered true}

/-- The world contains the room and a second table. -/
def world : Village Bool := {Fact.table true, Fact.table false, Fact.covered true}

theorem room_le_world : room ≤ world := by decide

/-- The situation pronoun satisfies the domain condition of *the table* although the world contains
two tables ((4) of ch. 9). -/
theorem incomplete_description :
    sentence (fun _ ↦ room) (fun x (s : Village Bool) ↦ Fact.table x ∈ s)
        (fun x s ↦ Fact.covered x ∈ s) world ≠ 0 ∧
      ¬ ∃! x, Fact.table x ∈ world :=
  ⟨(sentence_ne_zero_iff _ _ _ _).mpr ⟨true, by decide, by decide⟩, fun ⟨_, _, h⟩ ↦
    Bool.noConfusion ((h true (by decide)).trans (h false (by decide)).symm)⟩

section SloppyIdentity

variable {E : Type*}

/-- A relation-variable description `the [f v] NP`, §9.2.1, denotes the unique NP-satisfier
standing in the covert relation to the individual variable `v`, which a higher quantifier may
bind. -/
noncomputable def relDescription {S : Type*} (rel : E → E → S → Prop) (np : E → S → Prop) (v : E)
    (s : S) : Option E :=
  iota fun x ↦ np x s ∧ rel x v s

/-- The relation-variable description covaries with its individual variable, which licenses a sloppy
reading for (17b) of ch. 9 but wrongly also for (17a). -/
theorem relDescription_eq_some_iff {S : Type*} (rel : E → E → S → Prop) (np : E → S → Prop)
    (v : E) (s : S) (x : E) :
    relDescription rel np v s = some x ↔
      (np x s ∧ rel x v s) ∧ ∀ y, np y s → rel y v s → y = x := by
  rw [relDescription, iota_eq_some_iff]
  simp only [and_imp]

variable [DecidableEq E]

/-- In (29) of ch. 9, *every farmer who owns a donkey beats the donkey, and the priest beats the
donkey too*, with the LF (31), the quantifier scopes over the conjunction, and both occurrences of
*the donkey* are bound by `σ` to the same minimal situation. -/
noncomputable def everyOwnerBeatsTheDonkeyAndThePriestToo (s₀ s : Village E) : Prop :=
  every s₀ (ownsADonkey s₀)
    (fun x s s' ↦ Q (fun x s'' ↦ ∃ z ∈ the (fun z (s : Village E) ↦ Fact.donkey z ∈ s) s',
      Fact.beats x z ∈ s'' ∧
        ∃ p ∈ the (fun p (s : Village E) ↦ Fact.priest p ∈ s) s₀, Fact.beats p z ∈ s'') x s s') s

/-- On the situation-variable description, (32) of ch. 9 has only the strict reading, on which the
priest beats each farmer's donkey. -/
theorem everyOwnerBeatsTheDonkeyAndThePriestToo_iff (w : Village E) {p : E}
    (hp : the (fun p (s : Village E) ↦ Fact.priest p ∈ s) w = some p) :
    everyOwnerBeatsTheDonkeyAndThePriestToo w w ↔
      ∀ x y, Fact.farmer x ∈ w → Fact.donkey y ∈ w → Fact.owns x y ∈ w →
        Fact.beats x y ∈ w ∧ Fact.beats p y ∈ w := by
  have key (x y : E) : Q (fun x' s'' ↦ ∃ z ∈ the (fun z (s : Village E) ↦ Fact.donkey z ∈ s)
        {Fact.farmer x, Fact.donkey y, Fact.owns x y}, Fact.beats x' z ∈ s'' ∧
          ∃ p ∈ the (fun p (s : Village E) ↦ Fact.priest p ∈ s) w, Fact.beats p z ∈ s'')
        x w {Fact.farmer x, Fact.donkey y, Fact.owns x y} ↔
      {Fact.farmer x, Fact.donkey y, Fact.owns x y} ≤ w ∧
        Fact.beats x y ∈ w ∧ Fact.beats p y ∈ w := by
    rw [the_donkey_minimal, hp]
    simp only [Option.mem_def, Option.some.injEq, exists_eq_left']
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      Q_subset_iff (fun x ↦ {Fact.beats x y, Fact.beats p y}) x w
        {Fact.farmer x, Fact.donkey y, Fact.owns x y}
  constructor
  · intro h x y hf hd ho
    exact ((key x y).mp (h x _ ((minimal_ownsADonkey_iff w x _).mpr ⟨y, hf, hd, ho, rfl⟩))).2
  · intro h x s' hs
    obtain ⟨y, hf, hd, ho, rfl⟩ := (minimal_ownsADonkey_iff w x s').mp hs
    exact (key x y).mpr ⟨hs.prop.1, h x y hf hd ho⟩

end SloppyIdentity

/-! ### The data -/

section Data

open Examples

/-- The repeated description of a ch. 9 sloppy-identity row, bare or carrying a bound
relation. -/
inductive DescriptionType where
  | bare
  | relational
  deriving DecidableEq, Repr

/-- The description a row's `description` feature names. -/
def descriptionType? (e : Datum) : Option DescriptionType :=
  e.parse? "description" [("the donkey", .bare), ("the donkey he owns", .relational)]

/-- The sloppy-identity rows (17) of ch. 9: the strict reading is always available, and the
sloppy reading is out for the bare description, both occurrences bound to one minimal situation
(`everyOwnerBeatsTheDonkeyAndThePriestToo_iff`), and in for the relational one, which covaries
with its bound variable (`relDescription_eq_some_iff`). -/
theorem sloppy_rows : ∀ e ∈ Examples.all, ∀ d ∈ descriptionType? e,
    (∀ j ∈ e.readings.lookup "strict", j.band = .accepted) ∧
      ∀ j ∈ e.readings.lookup "sloppy",
        j.band = match d with | .bare => .rejected | .relational => .accepted := by
  decide

theorem sloppy_read : Datum.ReadCount descriptionType? Examples.all 2 := by decide

/-- The contrast rows of ch. 8, (22) and (31) with (33): the description under an agnostic
attitude is infelicitous (`attitude_eq_zero_of_agnostic`) while its Russellian paraphrase, the
row's alternative, is consistent (`russellian_consistent`). -/
theorem contrast_rows : ∀ e ∈ Examples.all, (e.feature? "contrast").isSome →
    ¬ e.JudgedFelicitous ∧ ∀ a ∈ e.alternatives, a.2 = .acceptable := by
  decide

theorem contrast_read :
    (Examples.all.filter fun e => (e.feature? "contrast").isSome).length = 2 := by decide

end Data

end Elbourne2013
