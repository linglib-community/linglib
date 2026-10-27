module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Cat
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Data.Examples.BaleKhanjian2014

/-!
# Bale & Khanjian 2014: syntactic complexity and competition in Western Armenian

Western Armenian singular nouns have general number — *dəgha* 'boy' is true of one boy or
of a group of boys — while plural nouns are strictly plural; yet a definite singular denotes
one boy. Gricean competition with the plural would strengthen every singular, and a purely
syntactic account that denies competition needs a stipulated singular for the null number
head and a stipulated ambiguity for numerals. What separates the cases is syntactic
complexity: the singular indefinite is a bare NP whose existential force comes from the verb,
so the plural indefinite, a full DP, is not among its structural alternatives and no
competition arises; a definite singular and a definite plural are both full DPs differing
in one head, so the plural competes, and the singular definite is read strictly. A numeral
makes the plural alternative available but synonymous, so nothing changes; and the definite
marker read as the supremum operator gives the plural a stronger local presupposition, which
Maximize Presupposition applied at that subconstituent uses to rule out a numeral on a
definite singular.

## Main definitions

* `general`, `strictPlural`, `two`: the denotations of the singular, the plural, and a
  numeral-modified noun over a set of boys.
* `sup?`: the supremum operator the definite marker denotes, defined on sets containing
  their own join.
* `singularIndef`, `pluralIndef`, `singularDef`, `pluralDef`, `numeralSg`, `numeralPl`: the
  paper's structures.

## References

* [bale-khanjian-2014]
* [katzir-2007] — structurally defined alternatives
* [bliss-2004] — the purely syntactic account
* [singh-2011] — Maximize Presupposition in local contexts
* [donabedian-1993] — general number in Western Armenian
* [link-1983] — the supremum operator
* [sauerland-2003], [krifka-1989], [spector-2007b] — number competition
-/

@[expose] public section

namespace BaleKhanjian2014

open PhraseStructure Tree

/-! ### Denotations -/

variable {α : Type*}

/-- The plural noun denotes the groups of two or more. -/
def strictPlural (B : Finset α) : Finset (Finset α) := B.powerset.filter (2 ≤ ·.card)

/-- A numeral restricts a noun to the groups of its cardinality. -/
def ofCard (n : ℕ) (P : Finset (Finset α)) : Finset (Finset α) := P.filter (·.card = n)

/-- *yergu* 'two'. -/
abbrev two (P : Finset (Finset α)) : Finset (Finset α) := ofCard 2 P

theorem mem_strictPlural {B x : Finset α} : x ∈ strictPlural B ↔ x ⊆ B ∧ 2 ≤ x.card := by
  simp [strictPlural]

variable [DecidableEq α]

/-- Over the boys `B`, the singular noun denotes every nonempty group of them. -/
def general (B : Finset α) : Finset (Finset α) := Finset.Ioc ∅ B

theorem mem_general {B x : Finset α} : x ∈ general B ↔ x ⊆ B ∧ x.Nonempty := by
  simp [general, and_comm]

theorem strictPlural_subset_general (B : Finset α) : strictPlural B ⊆ general B := fun x hx ↦ by
  rw [mem_strictPlural] at hx
  exact mem_general.2 ⟨hx.1, Finset.card_pos.1 (by omega)⟩

/-- Under a numeral the singular and the plural noun mean the same. -/
theorem two_general_eq_two_strictPlural (B : Finset α) :
    two (general B) = two (strictPlural B) := by
  ext x
  simp only [two, ofCard, Finset.mem_filter, mem_general, mem_strictPlural]
  constructor
  · rintro ⟨⟨h, -⟩, hc⟩; exact ⟨⟨h, by omega⟩, hc⟩
  · rintro ⟨⟨h, -⟩, hc⟩; exact ⟨⟨h, Finset.card_pos.1 (by omega)⟩, hc⟩

/-- The supremum operator returns the join of a set of groups when the set contains it. -/
def sup? (P : Finset (Finset α)) : Option (Finset α) :=
  if P.sup id ∈ P then some (P.sup id) else none

theorem sup_general (B : Finset α) : (general B).sup id = B := by
  apply le_antisymm (Finset.sup_le fun x hx ↦ (mem_general.1 hx).1)
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  · exact Finset.le_sup (f := id) (mem_general.2 ⟨subset_rfl, hB⟩)

theorem sup?_general (B : Finset α) : sup? (general B) = if B.Nonempty then some B else none := by
  rw [sup?, sup_general]
  by_cases hB : B.Nonempty
  · rw [ite_eq_left (mem_general.2 ⟨subset_rfl, hB⟩), ite_eq_left hB]
  · rw [ite_eq_right (fun h ↦ hB (mem_general.1 h).2), ite_eq_right hB]

theorem sup_strictPlural (B : Finset α) :
    (strictPlural B).sup id = if 2 ≤ B.card then B else ∅ := by
  split_ifs with h
  · apply le_antisymm (Finset.sup_le fun x hx ↦ (mem_strictPlural.1 hx).1)
    exact Finset.le_sup (f := id) (mem_strictPlural.2 ⟨subset_rfl, h⟩)
  · apply (Finset.sup_eq_bot_iff _ _).2
    intro x hx
    rw [mem_strictPlural] at hx
    exact absurd (le_trans hx.2 (Finset.card_le_card hx.1)) h

theorem sup?_strictPlural (B : Finset α) :
    sup? (strictPlural B) = if 2 ≤ B.card then some B else none := by
  rw [sup?, sup_strictPlural]
  by_cases h : 2 ≤ B.card
  · rw [ite_eq_left h, ite_eq_left (mem_strictPlural.2 ⟨subset_rfl, h⟩), ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right (fun hm ↦ absurd (mem_strictPlural.1 hm).2 (by simp)),
      ite_eq_right h]

/-- At the number phrase, the plural's presupposition is the stronger, since whenever the plural
    definite is defined so is the singular. -/
theorem strictPlural_presupposition_stronger (B : Finset α) :
    (sup? (strictPlural B)).isSome → (sup? (general B)).isSome := by
  rw [sup?_strictPlural, sup?_general]
  intro h
  split_ifs at h with h₁
  · simp [Finset.card_pos.1 (by omega : 0 < B.card)]
  · simp at h

/-- Read off the presuppositions, competition makes the singular definite denote a single boy
    exactly when the plural definite's presupposition fails. -/
theorem strict_singular_iff (B : Finset α) (hB : B.Nonempty) :
    (sup? (general B)).map Finset.card = some 1 ↔ sup? (strictPlural B) = none := by
  rw [sup?_general, sup?_strictPlural, ite_eq_left hB]
  have := Finset.card_pos.2 hB
  constructor
  · intro h; simp only [Option.map_some, Option.some.injEq] at h; rw [ite_eq_right (by omega)]
  · intro h; split_ifs at h with h₂; simp; omega

theorem sup?_two_eq (B : Finset α) : sup? (two (general B)) = sup? (two (strictPlural B)) := by
  rw [two_general_eq_two_strictPlural]

/-! ### The three boys -/

/-- The boys of the paper's context, and two named ones for the predicative sentences. -/
inductive Boy
  | john | brad | c
  deriving DecidableEq, Fintype, Repr

theorem denotations :
    general (Finset.univ : Finset Boy) =
      {{.john}, {.brad}, {.c}, {.john, .brad}, {.john, .c}, {.brad, .c}, {.john, .brad, .c}} ∧
    strictPlural (Finset.univ : Finset Boy) =
      {{.john, .brad}, {.john, .c}, {.brad, .c}, {.john, .brad, .c}} := by
  decide

/-! ### Structures -/

/-- The singular indefinite is a bare NP, the verb supplying existential force. -/
def singularIndef : Tree Cat String :=
  .node .S [.node .N [.terminal .N "dəgha"], .node .V [.terminal .V "vaze-ts"]]

/-- The plural indefinite is a full DP with a covert existential determiner. -/
def pluralIndef : Tree Cat String :=
  .node .S [
    .node .Det [.terminal .Det "∃",
      .node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-ner"]],
    .node .V [.terminal .V "vaze-ts-in"]]

/-- The singular definite is a full DP with a null number head. -/
def singularDef : Tree Cat String :=
  .node .S [
    .node .Det [.node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-∅"],
      .terminal .Det "-n"],
    .node .V [.terminal .V "vaze-ts"]]

/-- The plural definite has the same structure with the plural number head. -/
def pluralDef : Tree Cat String :=
  .node .S [
    .node .Det [.node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-ner"],
      .terminal .Det "-ə"],
    .node .V [.terminal .V "vaze-ts-in"]]

/-- The numeral-modified singular indefinite: a full DP, the numeral above the number
    phrase. -/
def numeralSg : Tree Cat String :=
  .node .S [
    .node .Det [.terminal .Det "∃",
      .node .Num [.terminal .Num "yergu",
        .node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-∅"]]],
    .node .V [.terminal .V "vaze-ts"]]

/-- The numeral-modified plural indefinite. -/
def numeralPl : Tree Cat String :=
  .node .S [
    .node .Det [.terminal .Det "∃",
      .node .Num [.terminal .Num "yergu",
        .node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-ner"]]],
    .node .V [.terminal .V "vaze-ts-in"]]

/-- The lexicon the substitutions draw on holds the two number heads, the two definite
    allomorphs, the two verb forms, and the noun. -/
def lexicon : Finset (Tree Cat String) :=
  {.terminal .Num "-∅", .terminal .Num "-ner", .terminal .Det "-n", .terminal .Det "-ə",
   .terminal .V "vaze-ts", .terminal .V "vaze-ts-in", .terminal .N "dəgha"}

/-- The plural indefinite is no structural alternative to the singular indefinite. It has a
    determiner phrase, and neither the singular indefinite nor the lexicon has one, so no chain
    of deletions, contractions and substitutions reaches it. -/
theorem pluralIndef_not_alternative :
    pluralIndef ∉ structuralAlternatives lexicon singularIndef := fun h ↦
  (by decide : ¬ ∀ s ∈ pluralIndef.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = .Det))
    (phrase_preservation _ .Det (forall_mem_substitutionSource.2 ⟨by decide, by decide⟩)
      (by decide) h)

/-- The plural definite is a structural alternative to the singular definite, and conversely:
    they differ by three same-category substitutions. -/
theorem pluralDef_alternative : equalComplexity (↑lexicon) singularDef pluralDef := by
  let step₁ : Tree Cat String :=
    .node .S [
      .node .Det [.node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-ner"],
        .terminal .Det "-ə"],
      .node .V [.terminal .V "vaze-ts"]]
  let step₂ : Tree Cat String :=
    .node .S [
      .node .Det [.node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-ner"],
        .terminal .Det "-n"],
      .node .V [.terminal .V "vaze-ts"]]
  refine ⟨?_, ?_⟩
  · refine .head (b := step₁) ?_ (.head (b := step₂) ?_ (.single ?_))
    · apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨0, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
    · apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
    · apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
  · refine .head (b := step₂) ?_ (.head (b := step₁) ?_ (.single ?_))
    · apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
    · apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
    · apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨0, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])

/-- The numeral-modified plural is a structural alternative to the numeral-modified singular,
    and conversely: the number head and the verb form substitute. -/
theorem numeralPl_alternative : equalComplexity lexicon numeralSg numeralPl := by
  let step : Tree Cat String :=
    .node .S [
      .node .Det [.terminal .Det "∃",
        .node .Num [.terminal .Num "yergu",
          .node .Num [.node .N [.terminal .N "dəgha"], .terminal .Num "-ner"]]],
      .node .V [.terminal .V "vaze-ts"]]
  refine ⟨?_, ?_⟩
  · refine .head (b := step) ?_ (.single ?_)
    · apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨0, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
    · apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
  · refine .head (b := step) ?_ (.single ?_)
    · apply StructuralOp.inChild ⟨0, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨1, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])
    · apply StructuralOp.inChild ⟨1, by simp⟩
      apply StructuralOp.inChild ⟨0, by simp⟩
      exact StructuralOp.subst rfl (by simp [lexicon])

/-! ### The rows -/

/-- The subject of a predicative sentence is John, or John and Brad. -/
def subject? (r : Datum) : Option (Finset Boy) :=
  match r.feature? "subject" with
  | some "atom" => some {.john}
  | some "group" => some {.john, .brad}
  | _ => none

/-- The denotation of a predicative sentence's noun phrase over the three boys, from its
    number and numeral. -/
def denotation? (r : Datum) : Option (Finset (Finset Boy)) :=
  if r.feature? "construction" = some "predicative" then
    let noun := match r.feature? "number" with
      | some "SG" => some (general Finset.univ)
      | some "PL" => some (strictPlural Finset.univ)
      | _ => none
    match r.feature? "numeral" with
    | some "two" => noun.map (ofCard 2)
    | some "one" => noun.map (ofCard 1)
    | _ => noun
  else none

/-- Each predicative sentence of the paper is acceptable exactly when its subject is in the
    denotation of its predicate: a single boy is a boy but not boys, and two boys are boys,
    two boys, and not one boy. -/
theorem rows_predication :
    ∀ r ∈ Examples.all, ∀ s ∈ subject? r, ∀ P ∈ denotation? r,
      (s ∈ P ↔ r.judgment = .acceptable) := by
  decide +kernel

end BaleKhanjian2014
