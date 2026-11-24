module

public import Linglib.Data.Examples.JereticEtAl2025
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.English.Determiners
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Strengthening
public import Linglib.Semantics.Reference.Iota

/-!
# Jeretič et al. (2025): Core concepts and indirect alternatives

French *tous* is odd in a domain known to hold two individuals, as English *all* is beside
*both*, though French has no word for *both*, and it is not odd in a domain of three. Jeretič,
Bassi, Gonzalez, Yatsushiro, Meyer and Sauerland take the dual of Harbour's number features to be
present in every language and null in French, so that the string *tous les NP* has a plural and a
dual parse.

For a spell-out `spell : P → S` of parses as strings, with a meaning and a node count for each
parse, the readings of a string are the meanings of its parses. A parse `q` bars a parse `p` when
`q` is at most as complex as `p` and means the same, and the string of `p` has a reading that the
string of `q` lacks. A parse is pronounceable when none bars it, and then its string is a least
ambiguous one, by inclusion of readings, among the parses that mean the same and are at most as
complex; the converse holds where those readings are comparable.

An indirect alternative of `s` is a pronounceable parse, at most as complex as `s`, that means
what an unpronounceable alternative of `s` means. A parse that bars an alternative of `s` is
therefore an indirect alternative of `s` once it is pronounceable and the alternative is at most
as complex as `s`.

A noun denotes the nonnull parts `Set.Ioc ⊥ c` of the sum `c` of its atoms, in an atomic
generalized Boolean algebra whose individuals have finitely many parts, which the number of atoms
grades. Harbour's features act on a region of given numbers of atoms as they act on those numbers,
so the dual `[+minimal]` over `[−atomic]` selects the parts with two atoms, as the numeral *deux*
does. Each parse thereby allows its subject's referent a set of numbers of atoms: the positive
numbers for a plural noun, two for a dual one, and with a numeral the number it names. The
definite article takes the largest member of its restrictor, which is `c` and exists exactly where
the number of atoms of `c` is one the parse allows.

The parses are those of *tous les verres sont pleins*, *les verres sont pleins*, *les deux verres
sont pleins* and *les trois verres sont pleins*, each with either value of `[±minimal]`. No
definite numeral is a structural alternative of the universal sentence, whose subject is a
quantifier phrase. The dual parse of the universal sentence is a structural alternative of the
plural one, and *les deux verres sont pleins* bars it, so the definite numeral with *deux* is an
indirect alternative of the plural parse and the one with *trois* is not. Strengthened by its
indirect alternatives, the presupposition of the plural parse holds where the cups number one or
more than two; strengthened by its pronounceable structural alternatives alone it is
unchanged. The dual parse of the plain definite is pronounceable, since every parse of another
string is more complex.

Across languages a plain quantifier is predicted to be odd in a domain of two when the language
has a dual expression for it with at most as many nodes, a lexical dual counting one. The
prediction is checked against the paper's judgments on nineteen sentences.

## Implementation notes

* The categories are those of the paper's bracketings. The quantifier `Q` is distinct from the
  determiner `D`, a distinction the Universal Dependencies categories of `PhraseStructure.Cat` do
  not draw, and the result that no determiner phrase is the subject of an alternative rests on it.
* `[±minimal]` is a null head between the determiner and the noun, so the spell-out of a parse is
  its yield without that head, and the two parses of a string differ in its value alone. The
  value `false` leaves the noun's region as it is and `true` applies `[+minimal]` to the exclusive
  `[−atomic]` region, the paper's exhaustified `[−atomic]`. Under the reading of a bundle at its
  positive values alone, `Number.dom`, the dual restricts nothing.
* A sentence denotes a trivalent proposition through `Presupposition.presupOfReferent`. The
  universal quantifier and the distributivity operator both say that every atom of the subject's
  referent is full, so *tous les NP* and *les NP* mean the same; homogeneity and non-maximality
  are not modelled.
* Equality of meanings is equality over the worlds of one model, so the results that need two
  meanings to differ take a world that separates them as a hypothesis.
* The grading by the number of atoms is `Mereology.gradeMinOrder`, a local instance here: on
  `Finset` it would stand beside mathlib's grading by cardinality.
* Node counts of the cross-linguistic cells follow the paper: *always* is *all* and *ways*,
  *toujours* is *tous* and *jours*, *immer* is suppletive for the same two heads, and the partitive
  *which of the two* has four.

## TODO

* The combination *tous les deux*, the restriction of Avoid Ambiguity to phase boundaries, and
  the rejected alternatives with a core concept *both* or with category-free replacement.
* The lexical duals of Japanese and Icelandic are not read from a fragment.
* That the plural parse of *tous les verres sont pleins* is pronounceable, which needs a model
  with a world that separates it from each definite numeral.

## References

* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
* [chemla-2007]
* [buccola-kriz-chemla-2022]
* [percus-2006]
* [sauerland-2008a]
* [harbour-2014]
* [katzir-2007]
-/

@[expose] public section

namespace JereticEtAl2025

/-! ### Avoid Ambiguity and indirect alternatives -/

section Blocking

variable {P S M : Type*} (spell : P → S) (meaning : P → M) (size : P → ℕ)

/-- The readings of a string are the meanings of its parses. -/
def readings (s : S) : Set M := meaning '' (spell ⁻¹' {s})

/-- (37): the parse `q` bars the parse `p` from pronunciation when `q` is at most as complex and
means the same, and the string of `p` has a reading that the string of `q` lacks. -/
structure Bars (q p : P) : Prop where
  /-- The barring parse is at most as complex as the barred one. -/
  size_le : size q ≤ size p
  /-- The two parses mean the same. -/
  meaning_eq : meaning q = meaning p
  /-- The string of `p` has a reading that the string of `q` lacks. -/
  not_subset : ¬ readings spell meaning (spell p) ⊆ readings spell meaning (spell q)

/-- A parse is pronounceable when no parse bars it. -/
def Pronounceable (p : P) : Prop := ∀ q, ¬ Bars spell meaning size q p

/-- (43): the indirect alternatives of `s` are the pronounceable parses at most as complex as `s`
that mean what some unpronounceable alternative of `s` means. -/
def indirect (alts : P → Set P) (s : P) : Set P :=
  {i | Pronounceable spell meaning size i ∧ size i ≤ size s ∧
    ∃ x ∈ alts s, ¬ Pronounceable spell meaning size x ∧ meaning i = meaning x}

variable {spell meaning size} {alts alts' : P → Set P} {p q s x : P}

theorem mem_readings {t : S} {a : M} :
    a ∈ readings spell meaning t ↔ ∃ p, spell p = t ∧ meaning p = a :=
  Iff.rfl

-- (37)
theorem bars_iff : Bars spell meaning size q p ↔ size q ≤ size p ∧ meaning q = meaning p ∧
    ∃ p₂, spell p₂ = spell p ∧ meaning p₂ ≠ meaning p ∧
      ∀ q₂, spell q₂ = spell q → meaning q₂ ≠ meaning p₂ := by
  refine ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, ?_⟩, fun ⟨h₁, h₂, p₂, hp₂, _, h⟩ ↦
    ⟨h₁, h₂, fun hs ↦ let ⟨q₂, hq₂, he⟩ := hs ⟨p₂, hp₂, rfl⟩; h q₂ hq₂ he⟩⟩
  obtain ⟨_, ⟨p₂, hp₂, rfl⟩, hn⟩ := Set.not_subset.1 h₃
  exact ⟨p₂, hp₂, fun he ↦ hn ⟨q, rfl, h₂.trans he.symm⟩, fun q₂ hq₂ he ↦ hn ⟨q₂, hq₂, he⟩⟩

theorem Bars.spell_ne (h : Bars spell meaning size q p) : spell q ≠ spell p :=
  fun he ↦ h.not_subset (he ▸ subset_rfl)

theorem pronounceable_of_forall_meaning_eq
    (h : ∀ p₂, spell p₂ = spell p → meaning p₂ = meaning p) :
    Pronounceable spell meaning size p := fun q hb ↦
  hb.not_subset fun _ ⟨p₂, hp₂, he⟩ ↦ ⟨q, rfl, hb.meaning_eq.trans ((h p₂ hp₂).symm.trans he)⟩

theorem Pronounceable.minimalFor (h : Pronounceable spell meaning size p) :
    MinimalFor (fun q ↦ meaning q = meaning p ∧ size q ≤ size p)
      (fun q ↦ readings spell meaning (spell q)) p :=
  ⟨⟨rfl, le_rfl⟩, fun q hq _ ↦ not_not.1 fun hn ↦ h q ⟨hq.2, hq.1, hn⟩⟩

theorem pronounceable_iff_minimalFor
    (hc : ∀ q, meaning q = meaning p →
      readings spell meaning (spell q) ⊆ readings spell meaning (spell p) ∨
        readings spell meaning (spell p) ⊆ readings spell meaning (spell q)) :
    Pronounceable spell meaning size p ↔
      MinimalFor (fun q ↦ meaning q = meaning p ∧ size q ≤ size p)
        (fun q ↦ readings spell meaning (spell q)) p :=
  ⟨Pronounceable.minimalFor, fun h q hb ↦ hb.not_subset
    ((hc q hb.meaning_eq).elim (h.2 ⟨hb.meaning_eq, hb.size_le⟩) id)⟩

theorem Bars.mem_indirect (h : Bars spell meaning size q x)
    (hq : Pronounceable spell meaning size q) (hx : x ∈ alts s) (hs : size x ≤ size s) :
    q ∈ indirect spell meaning size alts s :=
  ⟨hq, h.size_le.trans hs, x, hx, fun hp ↦ hp q h, h.meaning_eq⟩

theorem indirect_mono (h : alts s ⊆ alts' s) :
    indirect spell meaning size alts s ⊆ indirect spell meaning size alts' s :=
  fun _ ⟨hi, hs, x, hx, hp, hm⟩ ↦ ⟨hi, hs, x, h hx, hp, hm⟩

theorem indirect_eq_empty_of_forall_pronounceable
    (h : ∀ x ∈ alts s, Pronounceable spell meaning size x) :
    indirect spell meaning size alts s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, _, x, hx, hn, _⟩ ↦ hn (h x hx)

end Blocking

/-! ### Number and numerals as regions -/

section Region

open Mereology Number

/-- (93b), (102b): the dual is `[+minimal]` over `[−atomic]`. -/
def dual : Number.Bundle := {(.atomic, false), (.minimal, true)}

variable {D : Type*} [PartialOrder D] [OrderBot D]

/-- The region of a noun under a value of `[±minimal]` over `[−atomic]`: `[+minimal]` gives the
region of the dual (98b), and `[−minimal]`, like `[−atomic]`, selects all (94b), (95b). -/
def number (minimal : Bool) (P : Set D) : Set D := if minimal then dual.exact P else P

theorem number_subset (m : Bool) (P : Set D) : number m P ⊆ P := by
  cases m
  · exact subset_rfl
  · exact fun _ ↦ Bundle.exact_le dual P

theorem number_inter_of_isLowerSet (m : Bool) (P : Set D) {L : Set D} (hL : IsLowerSet L) :
    number m (P ∩ L) = number m P ∩ L := by
  cases m
  · rfl
  · exact Bundle.exact_inter_of_isLowerSet dual P hL

theorem number_grade_preimage [GradeMinOrder ℕ D] (m : Bool) (S : Set ℕ) :
    number m (grade ℕ ⁻¹' S : Set D) = grade ℕ ⁻¹' number m S := by
  cases m
  · rfl
  · exact Bundle.exact_grade_preimage dual S

-- (93b), (103)
theorem number_true_Ici_one : number true (Set.Ici 1 : Set ℕ) = {2} := by
  have h : Feature.restrict .atomic false (Set.Ici 1 : Set ℕ) = Set.Ici 2 := by
    ext k
    simp only [Feature.mem_restrict_atomic_false, Nat.isAtom_iff_eq_one, Set.mem_Ici]
    omega
  simp [number, dual, Bundle.exact, Bundle.step, h]

end Region

/-! ### The parses of (25) and (38) -/

/-- The categories of the bracketings in (38), with the head `Nb` of number below the
numeral. -/
inductive Cat where
  | Q
  | D
  | Num
  | Nb
  | N
  | V
  | S
  deriving DecidableEq, Repr

/-- The numerals of the fragment. -/
inductive Numeral where
  | deux
  | trois
  deriving DecidableEq, Repr

/-- The number a numeral names. -/
def Numeral.card : Numeral → ℕ
  | .deux => 2
  | .trois => 3

/-- The words of the fragment, among them the two values of `[±minimal]`. -/
inductive Word where
  | tous
  | les
  | numeral (n : Numeral)
  | minimal (v : Bool)
  | verres
  | sontPleins
  deriving DecidableEq, Repr

/-- The `[±minimal]` heads are null in French. -/
def Word.IsNull : Word → Prop
  | .minimal _ => True
  | _ => False

instance : DecidablePred Word.IsNull := fun w ↦ by
  cases w <;> unfold Word.IsNull <;> infer_instance

/-- The subjects of the fragment are *tous les NP*, *les NP* and *les n NP*. -/
inductive Subject where
  | tous
  | les
  | lesNum (n : Numeral)
  deriving DecidableEq, Repr

/-- A parse is a subject with a value of `[±minimal]` on its noun. -/
structure Parse where
  subject : Subject
  minimal : Bool
  deriving DecidableEq, Repr

open PhraseStructure Tree

/-- The noun phrase under its number head. -/
def nounPhrase (minimal : Bool) : Tree Cat Word :=
  .node .Nb [.terminal .Nb (.minimal minimal), .terminal .N .verres]

/-- (38): the tree of a subject, a quantifier phrase for *tous* and a determiner phrase
otherwise. -/
def Subject.tree (minimal : Bool) : Subject → Tree Cat Word
  | .tous => .node .Q [.terminal .Q .tous, .node .D [.terminal .D .les, nounPhrase minimal]]
  | .les => .node .D [.terminal .D .les, nounPhrase minimal]
  | .lesNum n =>
    .node .D [.terminal .D .les, .node .Num [.terminal .Num (.numeral n), nounPhrase minimal]]

namespace Parse

/-- The tree of a parse is its subject over the predicate *sont pleins*. -/
def tree (p : Parse) : Tree Cat Word :=
  .node .S [p.subject.tree p.minimal, .terminal .V .sontPleins]

/-- The string of a parse is its yield without the null heads. -/
def spell (p : Parse) : List Word := p.tree.yield.filter (¬ ·.IsNull)

/-- (38), (43): the complexity of a parse is the number of nodes of its tree. -/
def size (p : Parse) : ℕ := RoseTree.numNodes p.tree

end Parse

/-- The lexicon holds the words of the fragment under their categories. -/
def lexicon : Finset (Tree Cat Word) :=
  {.terminal .Q .tous, .terminal .D .les, .terminal .Num (.numeral .deux),
    .terminal .Num (.numeral .trois), .terminal .Nb (.minimal true),
    .terminal .Nb (.minimal false), .terminal .N .verres, .terminal .V .sontPleins}

/-- (42): the alternatives of a parse are the parses whose trees are structural alternatives of
its tree. -/
def Parse.alts (p : Parse) : Set Parse := {q | q.tree ∈ structuralAlternatives lexicon p.tree}

theorem Parse.spell_eq_spell_iff {p q : Parse} : p.spell = q.spell ↔ p.subject = q.subject := by
  rcases p with ⟨_ | _ | (_ | _), _ | _⟩ <;> rcases q with ⟨_ | _ | (_ | _), _ | _⟩ <;> decide

theorem Parse.size_les_lt (m m' : Bool) (s : Subject) (hs : s ≠ .les) :
    Parse.size ⟨.les, m⟩ < Parse.size ⟨s, m'⟩ := by
  rcases s with _ | _ | (_ | _) <;> cases m <;> cases m' <;> first | decide | exact absurd rfl hs

theorem Parse.size_lesNum_eq (n : Numeral) (m m' : Bool) :
    Parse.size ⟨.lesNum n, m⟩ = Parse.size ⟨.tous, m'⟩ := by
  cases n <;> cases m <;> cases m' <;> decide

theorem tous_true_mem_alts : (⟨.tous, true⟩ : Parse) ∈ Parse.alts ⟨.tous, false⟩ := by
  apply Relation.ReflTransGen.single
  apply RoseTree.Rewrites.set _ ⟨0, by simp⟩
  apply RoseTree.Rewrites.set _ ⟨1, by simp⟩
  apply RoseTree.Rewrites.set _ ⟨1, by simp⟩
  apply RoseTree.Rewrites.set _ ⟨0, by simp⟩
  refine .here (StructuralOp.subst rfl ?_)
  simp [substitutionSource, lexicon]

/-- No definite description, with a numeral or without, is a structural alternative of the
universal sentence: the subject of an alternative is never a determiner phrase. -/
theorem subject_eq_tous_of_mem_alts {m : Bool} {q : Parse} (h : q ∈ Parse.alts ⟨.tous, m⟩) :
    q.subject = .tous := by
  have hlic : q.tree.Licensed
      (fun l ks ↦ Label.cat l = Cat.S → ∀ k ∈ ks, Label.cat k ≠ Cat.D) :=
    licensed_of_atMostAsComplex
      (forall_mem_substitutionSource.2 ⟨by decide, by cases m <;> decide⟩)
      (fun _ _ _ _ h hS k hk ↦ h hS k (List.mem_of_mem_eraseIdx hk))
      (fun _ _ _ _ _ hc h hS x hx ↦ by
        rcases List.mem_append.1 hx with h₁ | h₂
        · exact h hS x (List.mem_append_left _ h₁)
        · rcases List.mem_cons.1 h₂ with rfl | h₃
          · exact hc ▸ h hS _ (by simp)
          · exact h hS x (by simp [h₃]))
      (by cases m <;> decide) h
  rcases q with ⟨_ | _ | n, m'⟩
  · rfl
  · exact absurd rfl (hlic.rel_root rfl _ List.mem_cons_self)
  · exact absurd rfl (hlic.rel_root rfl _ List.mem_cons_self)

/-! ### The meanings of the parses -/

section Meaning

open Mereology Presupposition

/-- The numbers of atoms a parse allows its subject's referent: those the number of its noun
selects from the positive numbers and, with a numeral, the one the numeral names. -/
def Parse.numerosity (p : Parse) : Set ℕ :=
  match p.subject with
  | .lesNum n => number p.minimal (Set.Ici 1) ∩ {n.card}
  | _ => number p.minimal (Set.Ici 1)

theorem Parse.numerosity_subset (p : Parse) : p.numerosity ⊆ Set.Ici 1 := by
  rcases p with ⟨_ | _ | n, m⟩
  · exact number_subset m _
  · exact number_subset m _
  · exact Set.inter_subset_left.trans (number_subset m _)

theorem numerosity_tous_false : Parse.numerosity ⟨.tous, false⟩ = Set.Ici 1 := rfl

theorem numerosity_tous_true : Parse.numerosity ⟨.tous, true⟩ = {2} := number_true_Ici_one

-- (40), (41)
theorem numerosity_lesNum_deux (m : Bool) : Parse.numerosity ⟨.lesNum .deux, m⟩ = {2} := by
  cases m
  · exact Set.ext fun k ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨by simp_all [number], h⟩⟩
  · exact (congrArg (· ∩ {2}) number_true_Ici_one).trans (Set.inter_self _)

theorem numerosity_lesNum_trois_subset (m : Bool) :
    Parse.numerosity ⟨.lesNum .trois, m⟩ ⊆ {3} := Set.inter_subset_right

variable {W E : Type*} [GeneralizedBooleanAlgebra E] [IsAtomic E] [LocallyFiniteOrderBot E]

/-- (26a): the members of a region with `n` atoms, the numeral's restriction. -/
def exactly (n : ℕ) (P : Set E) : Set E := {x ∈ P | atomCount E x = n}

/-- (26d), (28c), (39b): the restrictor of the definite in the subject of a parse, the region of
the noun under its number and, with a numeral, its members of that many atoms. -/
def Parse.region (p : Parse) (c : E) : Set E :=
  match p.subject with
  | .lesNum n => exactly n.card (number p.minimal (Set.Ioc ⊥ c))
  | _ => number p.minimal (Set.Ioc ⊥ c)

attribute [local instance] Mereology.gradeMinOrder

theorem Parse.region_eq (p : Parse) (c : E) :
    p.region c = {x | x ≤ c ∧ atomCount E x ∈ p.numerosity} := by
  have hIoc : Set.Ioc ⊥ c = (grade ℕ ⁻¹' Set.Ici 1 : Set E) ∩ Set.Iic c := Set.ext fun x ↦
    and_congr_left fun _ ↦
      ⟨fun hx ↦ by
        have h := grade_strictMono (𝕆 := ℕ) hx
        rw [grade_bot] at h
        exact Nat.one_le_iff_ne_zero.2 h.ne',
        fun h ↦ bot_lt_iff_ne_bot.2 fun hx ↦ by simp [hx, grade_bot] at h⟩
  have key (m : Bool) : number m (Set.Ioc ⊥ c) =
      {x | x ≤ c ∧ atomCount E x ∈ number m (Set.Ici 1)} := by
    rw [hIoc, number_inter_of_isLowerSet _ _ (IsLowerSet.Iic c), number_grade_preimage]
    exact Set.ext fun _ ↦ and_comm
  rcases p with ⟨_ | _ | n, m⟩
  · exact key m
  · exact key m
  · exact Set.ext fun x ↦ by
      simp only [Parse.region, exactly, key m, Parse.numerosity, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_singleton_iff, and_assoc]

theorem Parse.isGreatest_region_iff {p : Parse} {c x : E} :
    IsGreatest (p.region c) x ↔ x = c ∧ atomCount E c ∈ p.numerosity := by
  rw [Parse.region_eq]
  exact isGreatest_atomCount_mem_iff fun h ↦ absurd (p.numerosity_subset h) (by decide)

variable (c : W → E) (full : W → Set E)

/-- (27b), (28f), (40): a parse says of the largest member of its restrictor that its atoms are
all full, and is undefined where the restrictor has no largest member. -/
noncomputable def Parse.meaning (p : Parse) : W → Trivalent :=
  presupOfReferent (fun w ↦ iota {x | IsGreatest (p.region (c w)) x})
    fun x w ↦ atomsBelow x ⊆ full w

/-- The presupposition of a parse holds at the worlds where it is defined. -/
noncomputable def Parse.presup (p : Parse) : Set W := (Trivalent.gapExt (p.meaning c full))ᶜ

variable {c full} {p q : Parse} {w : W} {m : Bool}

theorem Parse.mem_presup_iff : w ∈ p.presup c full ↔ atomCount E (c w) ∈ p.numerosity := by
  have h : w ∈ p.presup c full ↔ ∃ x, IsGreatest (p.region (c w)) x := by
    simp only [Parse.presup, Set.mem_compl_iff, Trivalent.gapExt, Set.mem_ofPred_eq,
      Parse.meaning, presupOfReferent_eq_undefined_iff, not_not]
    exact iota_isGreatest_dom
  rw [h]
  simp only [Parse.isGreatest_region_iff, exists_eq_left]

theorem Parse.meaning_congr (h : p.numerosity = q.numerosity) :
    p.meaning c full = q.meaning c full := by
  simp only [Parse.meaning, Parse.region_eq, h]

omit [IsAtomic E] [LocallyFiniteOrderBot E] in
theorem Parse.presup_congr (h : p.meaning c full = q.meaning c full) :
    p.presup c full = q.presup c full := by
  rw [Parse.presup, Parse.presup, h]

-- (19b)
theorem Parse.meaning_apply_of_mem_presup (hp : w ∈ p.presup c full) (hq : w ∈ q.presup c full) :
    p.meaning c full w = q.meaning c full w :=
  (presupOfReferent_of_mem (referent := fun w ↦ iota {x | IsGreatest (p.region (c w)) x})
    (scope := fun x w ↦ atomsBelow x ⊆ full w) (e := c w) (mem_iota_isGreatest.2
      (Parse.isGreatest_region_iff.2 ⟨rfl, Parse.mem_presup_iff.1 hp⟩))).trans
    (presupOfReferent_of_mem (referent := fun w ↦ iota {x | IsGreatest (q.region (c w)) x})
      (scope := fun x w ↦ atomsBelow x ⊆ full w) (e := c w) (mem_iota_isGreatest.2
        (Parse.isGreatest_region_iff.2 ⟨rfl, Parse.mem_presup_iff.1 hq⟩))).symm

-- (40), (41)
theorem meaning_lesNum_deux :
    Parse.meaning c full ⟨.lesNum .deux, m⟩ = Parse.meaning c full ⟨.tous, true⟩ :=
  Parse.meaning_congr ((numerosity_lesNum_deux m).trans numerosity_tous_true.symm)

omit [IsAtomic E] [LocallyFiniteOrderBot E] in
theorem meaning_les : Parse.meaning c full ⟨.les, m⟩ = Parse.meaning c full ⟨.tous, m⟩ := rfl

theorem presup_tous_true_subset :
    Parse.presup c full ⟨.tous, true⟩ ⊆ Parse.presup c full ⟨.tous, false⟩ := fun _ h ↦
  Parse.mem_presup_iff.2 (Parse.numerosity_subset _ (Parse.mem_presup_iff.1 h))

end Meaning

/-! ### Blocking and competition -/

section Competition

open Mereology Presupposition

variable {W E : Type*} [GeneralizedBooleanAlgebra E] [IsAtomic E] [LocallyFiniteOrderBot E]
  {c : W → E} {full : W → Set E} {m : Bool}

local notation "Bars'" => Bars Parse.spell (Parse.meaning c full) Parse.size
local notation "Pronounceable'" => Pronounceable Parse.spell (Parse.meaning c full) Parse.size
local notation "indirect'" => indirect Parse.spell (Parse.meaning c full) Parse.size Parse.alts

theorem meaning_tous_ne (hw : ∃ w, atomCount E (c w) ∈ Set.Ici 1 \ {2}) :
    Parse.meaning c full ⟨.tous, false⟩ ≠ Parse.meaning c full ⟨.tous, true⟩ := fun h ↦ by
  obtain ⟨w, h₁, h₂⟩ := hw
  have hmem : w ∈ Parse.presup c full ⟨.tous, true⟩ :=
    Parse.presup_congr h ▸ Parse.mem_presup_iff.2 h₁
  exact h₂ (numerosity_tous_true ▸ Parse.mem_presup_iff.1 hmem)

/-- Avoid Ambiguity: *les deux verres sont pleins* bars the dual parse of *tous les verres sont
pleins*, in a model with a world whose cups are not two. -/
theorem bars_lesNum_deux_tous_true (hw : ∃ w, atomCount E (c w) ∈ Set.Ici 1 \ {2}) :
    Bars' ⟨.lesNum .deux, m⟩ ⟨.tous, true⟩ :=
  bars_iff.2 ⟨(Parse.size_lesNum_eq ..).le, meaning_lesNum_deux, ⟨.tous, false⟩,
    Parse.spell_eq_spell_iff.2 rfl, meaning_tous_ne hw, fun ⟨s, m'⟩ hs ↦ by
      obtain rfl : s = .lesNum .deux := Parse.spell_eq_spell_iff.1 hs
      exact fun h ↦ meaning_tous_ne hw (h.symm.trans meaning_lesNum_deux)⟩

theorem pronounceable_lesNum_deux : Pronounceable' ⟨.lesNum .deux, m⟩ :=
  pronounceable_of_forall_meaning_eq fun ⟨s, m'⟩ hs ↦ by
    obtain rfl : s = .lesNum .deux := Parse.spell_eq_spell_iff.1 hs
    exact meaning_lesNum_deux.trans meaning_lesNum_deux.symm

omit [IsAtomic E] [LocallyFiniteOrderBot E] in
-- (78)
theorem pronounceable_les : Pronounceable' ⟨.les, m⟩ := by
  rintro ⟨s, m'⟩ hb
  by_cases hs : s = .les
  · exact hb.spell_ne (Parse.spell_eq_spell_iff.2 hs)
  · exact (Parse.size_les_lt m m' s hs).not_ge hb.size_le

/-- *Les deux verres sont pleins* is an indirect alternative of the plural parse of *tous les
verres sont pleins*. -/
theorem lesNum_deux_mem_indirect (hw : ∃ w, atomCount E (c w) ∈ Set.Ici 1 \ {2}) :
    (⟨.lesNum .deux, m⟩ : Parse) ∈ indirect' ⟨.tous, false⟩ :=
  (bars_lesNum_deux_tous_true hw).mem_indirect pronounceable_lesNum_deux tous_true_mem_alts
    (by decide)

theorem lesNum_trois_notMem_indirect (h₂ : ∃ w, atomCount E (c w) = 2) :
    (⟨.lesNum .trois, m⟩ : Parse) ∉ indirect' ⟨.tous, false⟩ := by
  rintro ⟨-, -, ⟨s, m'⟩, hx, -, hm⟩
  obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
  obtain ⟨w, hw⟩ := h₂
  have hdual : w ∈ Parse.presup c full ⟨.tous, true⟩ :=
    Parse.mem_presup_iff.2 (numerosity_tous_true ▸ hw)
  have hmem : w ∈ Parse.presup c full ⟨.tous, m'⟩ := by
    cases m'
    · exact presup_tous_true_subset hdual
    · exact hdual
  have h3 : atomCount E (c w) = 3 :=
    numerosity_lesNum_trois_subset m (Parse.mem_presup_iff.1 (Parse.presup_congr hm ▸ hmem))
  omega

-- (19b)
theorem meaning_apply_of_mem_indirect {q : Parse} (hq : q ∈ indirect' ⟨.tous, false⟩) {w : W}
    (hw : w ∈ Parse.presup c full q) :
    Parse.meaning c full q w = Parse.meaning c full ⟨.tous, false⟩ w := by
  obtain ⟨-, -, ⟨s, m'⟩, hx, -, hm⟩ := hq
  obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
  have hw' : w ∈ Parse.presup c full ⟨.tous, m'⟩ := Parse.presup_congr hm ▸ hw
  rw [hm]
  cases m'
  · rfl
  · exact Parse.meaning_apply_of_mem_presup hw' (presup_tous_true_subset hw')

/-- Maximize Presupposition over indirect alternatives: the plural parse of *tous les verres sont
pleins* is used where the cups number one or more than two, in a model with such a world. -/
theorem strengthen_indirect_tous (hw : ∃ w, atomCount E (c w) ∈ Set.Ici 1 \ {2}) :
    strengthen indirect' (Parse.presup c full) ⟨.tous, false⟩ =
      {w | atomCount E (c w) ∈ Set.Ici 1 \ {2}} := by
  have hdeux : Parse.presup c full ⟨.lesNum .deux, false⟩ = Parse.presup c full ⟨.tous, true⟩ :=
    Parse.presup_congr meaning_lesNum_deux
  rw [strengthen_eq_sdiff (ψ := ⟨.lesNum .deux, false⟩) (lesNum_deux_mem_indirect hw), hdeux]
  · ext w
    rw [Set.mem_sdiff, Parse.mem_presup_iff, Parse.mem_presup_iff, numerosity_tous_true]
    rfl
  · rw [hdeux]
    refine ⟨presup_tous_true_subset, fun h ↦ ?_⟩
    obtain ⟨w, h₁, h₂⟩ := hw
    exact h₂ (numerosity_tous_true ▸ Parse.mem_presup_iff.1 (h (Parse.mem_presup_iff.2 h₁)))
  · rintro χ ⟨-, -, ⟨s, m'⟩, hx, -, hm⟩ hss
    obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
    rw [Parse.presup_congr hm, hdeux] at *
    cases m'
    · exact absurd rfl hss.ne
    · exact subset_rfl

-- (2a)
theorem strengthen_pronounceable_tous (hw : ∃ w, atomCount E (c w) ∈ Set.Ici 1 \ {2}) :
    strengthen (fun p ↦ {q ∈ p.alts | Pronounceable' q}) (Parse.presup c full) ⟨.tous, false⟩ =
      Parse.presup c full ⟨.tous, false⟩ := by
  refine strengthen_eq_self ?_
  rintro ⟨s, m'⟩ ⟨hx, hp⟩ hss
  obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
  cases m'
  · exact hss.ne rfl
  · exact hp _ (bars_lesNum_deux_tous_true (m := false) hw)

end Competition

/-! ### Other quantifiers and other languages -/

/-- A dual expression of a language is a lexical item or a phrase with a count of nodes. -/
inductive DualForm where
  | lexical
  | phrase (size : ℕ)
  deriving DecidableEq, Repr

/-- The node count of a dual expression, a lexical item counting one. -/
def DualForm.size : DualForm → ℕ
  | .lexical => 1
  | .phrase n => n

/-- A determiner of a fragment is a lexical dual when its number restriction is the dual. -/
def DualForm.ofDeterminer (d : QuantificationalDeterminer) : List DualForm :=
  if d.numberRestriction = some .dual then [.lexical] else []

/-- The plain expression of a quantifier in a language, by its node count, with the dual
expressions the language has for it. -/
structure Cell where
  plain : ℕ
  duals : List DualForm
  deriving DecidableEq, Repr

/-- A plain quantifier is predicted to be odd in a domain of two when some dual expression is at
most as complex: a lexical dual is a structural alternative, and a phrase bars the dual parse and
stands in for it as an indirect alternative. -/
def Cell.AntiDual (c : Cell) : Prop := ∃ d ∈ c.duals, d.size ≤ c.plain

instance : DecidablePred Cell.AntiDual := fun c ↦ by unfold Cell.AntiDual; infer_instance

open Examples in
/-- English: *both* and *neither*, the partitives *which*, *each* and *one of the two*, and
*both times* beside *always*. -/
def english : Slot → Option Cell
  | .universal => some ⟨1, DualForm.ofDeterminer English.Determiners.both⟩
  | .negative => some ⟨1, DualForm.ofDeterminer English.Determiners.neither⟩
  | .which | .each | .one => some ⟨1, [.phrase 4]⟩
  | .always => some ⟨2, [.phrase 2]⟩
  | .definite => none

open Examples in
/-- French: *les deux NP* beside *tous les NP*, *aucun des deux* and *ni l'un ni l'autre* beside
*aucun*, and *les deux fois* beside *toujours*. -/
def french : Slot → Option Cell
  | .universal => some ⟨3, [.phrase 3]⟩
  | .negative => some ⟨1, [.phrase 3, .phrase 5]⟩
  | .which | .each | .one => some ⟨1, []⟩
  | .always => some ⟨2, [.phrase 3]⟩
  | .definite => none

open Examples in
/-- German: no dual beside *keine*, and *beide Male* beside *immer*. -/
def german : Slot → Option Cell
  | .negative => some ⟨1, []⟩
  | .always => some ⟨2, [.phrase 2]⟩
  | _ => none

open Examples in
/-- Japanese: the dual indeterminate *dotti* beside *dono*, and *ni-kai* and *ni-kai-to-mo* beside
*itu-mo*. -/
def japanese : Slot → Option Cell
  | .which | .each | .one => some ⟨1, [.lexical]⟩
  | .always => some ⟨2, [.phrase 2, .phrase 4]⟩
  | _ => none

open Examples in
/-- Icelandic: the dual *hvor* beside *hvaða*. -/
def icelandic : Slot → Option Cell
  | .which => some ⟨1, [.lexical]⟩
  | _ => none

/-- The cell of a row with the plain expression of a slot. -/
def cell (e : Datum) : Option Cell := do
  let language ← e.byLanguage [(.english, english), (.french, french), (.german, german),
    (.japanese, japanese), (.icelandic, icelandic)]
  let slot ← Examples.slot e
  if Examples.marking e = some .plain then language slot else none

/-- A plain quantifier is less than acceptable in a domain of two exactly where its language has
a dual expression at most as complex, in each of the nineteen sentences. -/
theorem antiDual_iff_not_accepted :
    (∀ e ∈ Examples.all, ∀ c ∈ cell e, (c.AntiDual ↔ e.judgment.band ≠ .accepted)) ∧
      Datum.ReadCount cell Examples.all 19 := by
  decide

-- §5.4
theorem antiDual_of_phrase :
    ∀ c ∈ [french .universal, english .always, german .always, japanese .always].filterMap id,
      c.AntiDual ∧ DualForm.lexical ∉ c.duals := by
  decide

end JereticEtAl2025
