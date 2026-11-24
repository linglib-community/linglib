module

public import Linglib.Data.Examples.JereticEtAl2025
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.English.Determiners
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Plurality.Number
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

A noun denotes the nonnull parts `Set.Ioc ⊥ c` of the sum `c` of its atoms. The dual
`[+minimal]` over `[−atomic]` selects the parts with two atoms, as the numeral *deux* does, and the
definite article takes the largest member of its restrictor, so *les deux NP* and *tous les NP*
with a dual noun both refer to `c` where it has two atoms and are undefined elsewhere, while
*tous les NP* with a plural noun refers to `c` wherever it is not null.

The parses are those of *tous les verres sont pleins*, *les verres sont pleins*, *les deux verres
sont pleins* and *les trois verres sont pleins*, each with either value of `[±minimal]`. No
definite numeral is a structural alternative of the universal sentence, whose subject is a
quantifier phrase. The dual parse of the universal sentence is a structural alternative of the
plural one, and *les deux verres sont pleins* bars it, so the definite numeral with *deux* is an
indirect alternative of the plural parse and the one with *trois* is not. Strengthened by its
indirect alternatives, the presupposition of the plural parse holds where there are cups and
they are not two; strengthened by its pronounceable structural alternatives alone it is
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
* [buccola-kriz-chemla-2018]
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

/-! ### The dual and the definite numeral -/

section Region

open Mereology Number

/-- (26a): the members of a region with `n` atoms, the numeral's restriction. -/
def exactly {E : Type*} [PartialOrder E] [OrderBot E] (n : ℕ) (P : Set E) : Set E :=
  {x ∈ P | atomCount E x = n}

/-- The region of a noun under a value of `[±minimal]` over `[−atomic]`: `[+minimal]` selects
the minimal members that are not atoms, the dual (98b), and `[−minimal]` selects all (95b). -/
def number {E : Type*} [PartialOrder E] [OrderBot E] (minimal : Bool) (P : Set E) : Set E :=
  if minimal then atomize (Feature.restrict .atomic false P) else P

variable {E : Type*} [GeneralizedBooleanAlgebra E] [IsAtomic E] {c x : E} {m n : ℕ}

omit [IsAtomic E] in
theorem exactly_Ioc (hn : n ≠ 0) :
    exactly n (Set.Ioc ⊥ c) = {x | x ≤ c ∧ atomCount E x = n} :=
  Set.ext fun x ↦ ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦
    ⟨⟨bot_lt_iff_ne_bot.2 fun hx ↦ hn (by rw [← h.2, hx, atomCount_bot]), h.1⟩, h.2⟩⟩

-- (103)
theorem number_true_Ioc : number true (Set.Ioc ⊥ c) = exactly 2 (Set.Ioc ⊥ c) := by
  rw [exactly_Ioc two_ne_zero]
  exact Set.ext fun _ ↦ mem_atomize_restrict_atomic_false_Ioc

omit [IsAtomic E] in
theorem exactly_exactly (P : Set E) : exactly n (exactly n P) = exactly n P :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.2⟩⟩

omit [IsAtomic E] in
theorem exactly_exactly_of_ne (h : m ≠ n) (P : Set E) : exactly n (exactly m P) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦ h (hx.1.2.symm.trans hx.2)

theorem isGreatest_exactly_Ioc (hn : n ≠ 0) :
    IsGreatest (exactly n (Set.Ioc ⊥ c)) x ↔ x = c ∧ atomCount E c = n := by
  rw [exactly_Ioc hn]
  exact isGreatest_atomCount_iff hn

omit [IsAtomic E] in
theorem isGreatest_Ioc_bot : IsGreatest (Set.Ioc ⊥ c) x ↔ x = c ∧ c ≠ ⊥ :=
  ⟨fun h ↦ ⟨h.1.2.antisymm (h.2 ⟨h.1.1.trans_le h.1.2, le_rfl⟩), (h.1.1.trans_le h.1.2).ne'⟩,
    by rintro ⟨rfl, hc⟩; exact ⟨⟨bot_lt_iff_ne_bot.2 hc, le_rfl⟩, fun _ h ↦ h.2⟩⟩

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

variable {W E : Type*} [GeneralizedBooleanAlgebra E]

/-- (26d), (28c), (39b): the restrictor of the definite in the subject of a parse, the region of
the noun under its number and, with a numeral, its members of that many atoms. -/
def Parse.region (p : Parse) (c : E) : Set E :=
  match p.subject with
  | .lesNum n => exactly n.card (number p.minimal (Set.Ioc ⊥ c))
  | _ => number p.minimal (Set.Ioc ⊥ c)

variable (c : W → E) (full : W → Set E)

/-- (27b), (28f), (40): a parse says of the largest member of its restrictor that its atoms are
all full, and is undefined where the restrictor has no largest member. -/
noncomputable def Parse.meaning (p : Parse) : W → Trivalent :=
  presupOfReferent (fun w ↦ iota {x | IsGreatest (p.region (c w)) x})
    fun x w ↦ atomsBelow x ⊆ full w

/-- The presupposition of a parse holds at the worlds where it is defined. -/
noncomputable def Parse.presup (p : Parse) : Set W := (Trivalent.gapExt (p.meaning c full))ᶜ

variable {c full} {p q : Parse} {w : W} {m : Bool}

theorem Parse.mem_presup_iff : w ∈ p.presup c full ↔ ∃ x, IsGreatest (p.region (c w)) x := by
  simp only [Parse.presup, Set.mem_compl_iff, Trivalent.gapExt, Set.mem_ofPred_eq, Parse.meaning,
    presupOfReferent_eq_undefined_iff, not_not, iota_isGreatest_dom]

theorem Parse.meaning_congr (h : ∀ c : E, p.region c = q.region c) :
    p.meaning c full = q.meaning c full := by
  simp only [Parse.meaning, h]

theorem Parse.presup_congr (h : p.meaning c full = q.meaning c full) :
    p.presup c full = q.presup c full := by
  rw [Parse.presup, Parse.presup, h]

theorem Parse.meaning_apply_of_isGreatest {x : E} (hp : IsGreatest (p.region (c w)) x)
    (hq : IsGreatest (q.region (c w)) x) : p.meaning c full w = q.meaning c full w :=
  (presupOfReferent_of_mem (referent := fun w ↦ iota {x | IsGreatest (p.region (c w)) x})
    (scope := fun x w ↦ atomsBelow x ⊆ full w) (mem_iota_isGreatest.2 hp)).trans
    (presupOfReferent_of_mem (referent := fun w ↦ iota {x | IsGreatest (q.region (c w)) x})
      (scope := fun x w ↦ atomsBelow x ⊆ full w) (mem_iota_isGreatest.2 hq)).symm

theorem meaning_les : Parse.meaning c full ⟨.les, m⟩ = Parse.meaning c full ⟨.tous, m⟩ := rfl

variable [IsAtomic E]

theorem region_dual (c : E) : Parse.region ⟨.tous, true⟩ c = exactly 2 (Set.Ioc ⊥ c) :=
  number_true_Ioc

-- (40), (41)
theorem region_lesNum_deux (c : E) :
    Parse.region ⟨.lesNum .deux, m⟩ c = Parse.region ⟨.tous, true⟩ c := by
  cases m
  · exact number_true_Ioc.symm
  · exact (congrArg (exactly 2) number_true_Ioc).trans
      ((exactly_exactly _).trans number_true_Ioc.symm)

-- (40), (41)
theorem meaning_lesNum_deux :
    Parse.meaning c full ⟨.lesNum .deux, m⟩ = Parse.meaning c full ⟨.tous, true⟩ :=
  Parse.meaning_congr region_lesNum_deux

omit [IsAtomic E] in
theorem presup_tous_false : Parse.presup c full ⟨.tous, false⟩ = {w | c w ≠ ⊥} :=
  Set.ext fun _ ↦ Parse.mem_presup_iff.trans
    ⟨fun ⟨_, h⟩ ↦ (isGreatest_Ioc_bot.1 h).2, fun h ↦ ⟨_, isGreatest_Ioc_bot.2 ⟨rfl, h⟩⟩⟩

theorem presup_tous_true :
    Parse.presup c full ⟨.tous, true⟩ = {w | atomCount E (c w) = 2} :=
  Set.ext fun w ↦ Parse.mem_presup_iff.trans <| by
    rw [region_dual]
    exact ⟨fun ⟨_, h⟩ ↦ ((isGreatest_exactly_Ioc two_ne_zero).1 h).2,
      fun h ↦ ⟨_, (isGreatest_exactly_Ioc two_ne_zero).2 ⟨rfl, h⟩⟩⟩

theorem presup_lesNum_trois_subset :
    Parse.presup c full ⟨.lesNum .trois, m⟩ ⊆ {w | atomCount E (c w) = 3} := fun w hw ↦ by
  obtain ⟨x, hx⟩ := Parse.mem_presup_iff.1 hw
  cases m
  · exact ((isGreatest_exactly_Ioc three_ne_zero).1 hx).2
  · have h : Parse.region ⟨.lesNum .trois, true⟩ (c w) = ∅ :=
      (congrArg (exactly 3) number_true_Ioc).trans (exactly_exactly_of_ne (by decide) _)
    exact absurd hx.1 (h ▸ Set.notMem_empty x)

theorem presup_tous_true_subset :
    Parse.presup c full ⟨.tous, true⟩ ⊆ Parse.presup c full ⟨.tous, false⟩ := by
  rw [presup_tous_true, presup_tous_false]
  rintro w (hw : atomCount E (c w) = 2) h
  simp [h] at hw

-- (19b)
theorem meaning_tous_apply_of_atomCount (h : atomCount E (c w) = 2) :
    Parse.meaning c full ⟨.tous, false⟩ w = Parse.meaning c full ⟨.tous, true⟩ w := by
  have hc : c w ≠ ⊥ := fun hc ↦ by simp [hc] at h
  exact Parse.meaning_apply_of_isGreatest (isGreatest_Ioc_bot.2 ⟨rfl, hc⟩)
    (region_dual (c w) ▸ (isGreatest_exactly_Ioc two_ne_zero).2 ⟨rfl, h⟩)

end Meaning

/-! ### Blocking and competition -/

section Competition

open Mereology Presupposition

variable {W E : Type*} [GeneralizedBooleanAlgebra E] [IsAtomic E] {c : W → E} {full : W → Set E}
  {m : Bool}

local notation "Bars'" => Bars Parse.spell (Parse.meaning c full) Parse.size
local notation "Pronounceable'" => Pronounceable Parse.spell (Parse.meaning c full) Parse.size
local notation "indirect'" => indirect Parse.spell (Parse.meaning c full) Parse.size Parse.alts

theorem meaning_tous_ne (hw : ∃ w, c w ≠ ⊥ ∧ atomCount E (c w) ≠ 2) :
    Parse.meaning c full ⟨.tous, false⟩ ≠ Parse.meaning c full ⟨.tous, true⟩ := fun h ↦ by
  obtain ⟨w, hc, hn⟩ := hw
  have := Parse.presup_congr h
  rw [presup_tous_false, presup_tous_true] at this
  exact hn (this ▸ hc : w ∈ {w | atomCount E (c w) = 2})

/-- Avoid Ambiguity: *les deux verres sont pleins* bars the dual parse of *tous les verres sont
pleins*, in a model with a world whose cups are not two. -/
theorem bars_lesNum_deux_tous_true (hw : ∃ w, c w ≠ ⊥ ∧ atomCount E (c w) ≠ 2) :
    Bars' ⟨.lesNum .deux, m⟩ ⟨.tous, true⟩ :=
  bars_iff.2 ⟨(Parse.size_lesNum_eq ..).le, meaning_lesNum_deux, ⟨.tous, false⟩,
    Parse.spell_eq_spell_iff.2 rfl, meaning_tous_ne hw, fun ⟨s, m'⟩ hs ↦ by
      obtain rfl : s = .lesNum .deux := Parse.spell_eq_spell_iff.1 hs
      exact fun h ↦ meaning_tous_ne hw (h.symm.trans meaning_lesNum_deux)⟩

theorem pronounceable_lesNum_deux : Pronounceable' ⟨.lesNum .deux, m⟩ :=
  pronounceable_of_forall_meaning_eq fun ⟨s, m'⟩ hs ↦ by
    obtain rfl : s = .lesNum .deux := Parse.spell_eq_spell_iff.1 hs
    exact meaning_lesNum_deux.trans meaning_lesNum_deux.symm

omit [IsAtomic E] in
-- (78)
theorem pronounceable_les : Pronounceable' ⟨.les, m⟩ := by
  rintro ⟨s, m'⟩ hb
  by_cases hs : s = .les
  · exact hb.spell_ne (Parse.spell_eq_spell_iff.2 hs)
  · exact (Parse.size_les_lt m m' s hs).not_ge hb.size_le

/-- *Les deux verres sont pleins* is an indirect alternative of the plural parse of *tous les
verres sont pleins*. -/
theorem lesNum_deux_mem_indirect (hw : ∃ w, c w ≠ ⊥ ∧ atomCount E (c w) ≠ 2) :
    (⟨.lesNum .deux, m⟩ : Parse) ∈ indirect' ⟨.tous, false⟩ :=
  (bars_lesNum_deux_tous_true hw).mem_indirect pronounceable_lesNum_deux tous_true_mem_alts
    (by decide)

theorem lesNum_trois_notMem_indirect (h₂ : ∃ w, atomCount E (c w) = 2) :
    (⟨.lesNum .trois, m⟩ : Parse) ∉ indirect' ⟨.tous, false⟩ := by
  rintro ⟨-, -, ⟨s, m'⟩, hx, -, hm⟩
  obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
  obtain ⟨w, hw⟩ := h₂
  have hdual : w ∈ Parse.presup c full ⟨.tous, true⟩ := by rwa [presup_tous_true]
  have hmem : w ∈ Parse.presup c full ⟨.tous, m'⟩ := by
    cases m'
    · exact presup_tous_true_subset hdual
    · exact hdual
  have h3 : atomCount E (c w) = 3 := presup_lesNum_trois_subset (Parse.presup_congr hm ▸ hmem)
  omega

-- (19b)
theorem meaning_apply_of_mem_indirect {q : Parse} (hq : q ∈ indirect' ⟨.tous, false⟩) {w : W}
    (hw : w ∈ Parse.presup c full q) :
    Parse.meaning c full q w = Parse.meaning c full ⟨.tous, false⟩ w := by
  obtain ⟨-, -, ⟨s, m'⟩, hx, -, hm⟩ := hq
  obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
  cases m'
  · rw [hm]
  · have hdual : w ∈ Parse.presup c full ⟨.tous, true⟩ := Parse.presup_congr hm ▸ hw
    rw [presup_tous_true] at hdual
    rw [hm, meaning_tous_apply_of_atomCount hdual]

/-- Maximize Presupposition over indirect alternatives: the plural parse of *tous les verres sont
pleins* is used where there are cups and they are not two, in a model with such a world. -/
theorem strengthen_indirect_tous (hw : ∃ w, c w ≠ ⊥ ∧ atomCount E (c w) ≠ 2) :
    strengthen indirect' (Parse.presup c full) ⟨.tous, false⟩ =
      {w | c w ≠ ⊥ ∧ atomCount E (c w) ≠ 2} := by
  rw [strengthen_eq_sdiff (ψ := ⟨.lesNum .deux, false⟩) (lesNum_deux_mem_indirect hw),
    Parse.presup_congr meaning_lesNum_deux, presup_tous_false, presup_tous_true]
  · rfl
  · rw [Parse.presup_congr meaning_lesNum_deux]
    exact ⟨presup_tous_true_subset, fun h ↦ meaning_tous_ne (full := full) hw <| by
      obtain ⟨w, hc, hn⟩ := hw
      rw [presup_tous_false, presup_tous_true] at h
      exact absurd (h hc) hn⟩
  · rintro χ ⟨-, -, ⟨s, m'⟩, hx, -, hm⟩ hss
    obtain rfl : s = .tous := subject_eq_tous_of_mem_alts hx
    rw [Parse.presup_congr hm, Parse.presup_congr meaning_lesNum_deux] at *
    cases m'
    · exact absurd rfl hss.ne
    · exact subset_rfl

-- (2a)
theorem strengthen_pronounceable_tous (hw : ∃ w, c w ≠ ⊥ ∧ atomCount E (c w) ≠ 2) :
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
