module

public import Linglib.Core.Computability.ShuffleIdeal
public import Linglib.Core.Computability.ContextFreeGrammar.Regular
public import Linglib.Core.Computability.ContextFreeGrammar.Map
public import Linglib.Core.Computability.NonContextFree.AmBnCmDn
public import Linglib.Fragments.German.Zurich.Verbs
public import Linglib.Data.Examples.Shieber1985
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.DeriveFintype

/-!
# Shieber (1985): Evidence Against the Context-Freeness of Natural Language

This file proves Shieber's theorem that a language meeting his four claims about Swiss German
subordinate clauses is not context-free. The homomorphism `f` sends the words of the clauses to
letters, and the image of the language intersected with the regular language
`r = w a* b* x c* d* y` is `w aᵐ bⁿ x cᵐ dⁿ y`. Erasing `w`, `x` and `y` leaves `aᵐ bⁿ cᵐ dⁿ`,
which is not context-free, and the context-free languages are closed under homomorphisms and
under intersection with regular languages.

## Main definitions

* `Letter`: the letters of the image of `f`
* `caseSorted`: the regular language `r`
* `Claims f L`: the four claims about a language `L` whose words `f` sends to letters

## Main results

* `Claims.map_inf_caseSorted`: the image of the language intersected with `r`
* `Claims.not_isContextFree`: a language meeting the claims is not context-free
* `not_isContextFree_of_count_le`: the same with optional objects, under a one-sided Claim 3
* `acceptable_iff_perm`: Claim 3 against the paper's clauses (1)–(22)

## Implementation notes

The letters put the accusative *d'chind* and *laa* before the dative *em Hans* and *hälfe*, as the
schema of Claim 2 and `f` do; the prose of Claim 2 puts the datives first. In the data, a verb
requires the case of its entry in `German.Zurich.Verbs`, and a noun phrase bears the case its
gloss marks.

## TODO

Note 4 restricts Claim 3 to clauses with as many noun phrases as verbs, which does not suffice:
the image, with the frame erased, can then be `{aᵖ bᵠ cʳ dᵘ | p + q ≠ r + u} ∪ {aᵐ bⁿ cᵐ dⁿ}`,
the union of the context-free `{aᵖ bᵠ cʳ dᵘ | p + q ≠ r + u}` and `{aᵏ bʲ cᵏ dˡ}`. Stating the
counterexample needs the closure of the context-free languages under union.

## References

* [shieber-1985]
* [hopcroft-ullman-1979]
* [bar-hillel-perles-shamir-1961]
-/

@[expose] public section

namespace Shieber1985

/-! ### The letters and the regular language `r` -/

/-- `Letter` is the alphabet of the image of `f`, its letters declared in the order of
`r = w a* b* x c* d* y`. -/
inductive Letter
  /-- `w` is the image of *Jan säit das mer* 'Jan says that we'. -/
  | w
  /-- `a` is the image of the accusative *d'chind* 'the children'. -/
  | a
  /-- `b` is the image of the dative *em Hans* 'Hans'. -/
  | b
  /-- `x` is the image of *es huus haend wele* 'the house have wanted'. -/
  | x
  /-- `c` is the image of *laa* 'let', which requires an accusative. -/
  | c
  /-- `d` is the image of *hälfe* 'help', which requires a dative. -/
  | d
  /-- `y` is the image of *aastriiche* 'paint'. -/
  | y
  /-- `z` is the image of any other word. -/
  | z
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Letter := LinearOrder.lift' Letter.ctorIdx (by decide)

private theorem Letter.le_def {ℓ ℓ' : Letter} : ℓ ≤ ℓ' ↔ ℓ.ctorIdx ≤ ℓ'.ctorIdx := Iff.rfl

open Letter List Language

/-- `clause p q r u` is `w aᵖ bᵠ x cʳ dᵘ y`, the image of the clause with `p` *d'chind*,
`q` *em Hans*, `r` *laa* and `u` *hälfe*. -/
def clause (p q r u : ℕ) : List Letter :=
  w :: replicate p a ++ replicate q b ++ x :: replicate r c ++ replicate u d ++ [y]

/-- `schema` is `w (a|b)* x (c|d)* y`, the images of the clauses of the schema of Claim 1. -/
def schema : Language Letter :=
  {l | ∃ nps vs : List Letter, (∀ ℓ ∈ nps, ℓ = a ∨ ℓ = b) ∧ (∀ ℓ ∈ vs, ℓ = c ∨ ℓ = d) ∧
    l = w :: nps ++ x :: vs ++ [y]}

/-- `caseSorted` is the regular language `r = w a* b* x c* d* y`, the images of the clauses of
the schema of Claim 2. -/
def caseSorted : Language Letter := {l | ∃ p q r u, l = clause p q r u}

/-- `crossSerial` is the language `w aᵐ bⁿ x cᵐ dⁿ y`. -/
def crossSerial : Language Letter := {l | ∃ m n, l = clause m n m n}

theorem sortedLE_clause (p q r u : ℕ) : (clause p q r u).SortedLE := by
  simp +decide [clause, sortedLE_iff_pairwise, pairwise_append, pairwise_replicate,
    mem_replicate, Letter.le_def, or_imp, forall_and]

theorem count_clause (p q r u : ℕ) (ℓ : Letter) :
    (clause p q r u).count ℓ = match ℓ with
      | w | x | y => 1 | a => p | b => q | c => r | d => u | z => 0 := by
  cases ℓ <;> simp [clause, count_replicate]

theorem clause_mem_schema (p q r u : ℕ) : clause p q r u ∈ schema :=
  ⟨replicate p a ++ replicate q b, replicate r c ++ replicate u d,
    by simp +contextual [mem_replicate, or_imp], by simp +contextual [mem_replicate, or_imp],
    by simp [clause]⟩

theorem mem_caseSorted_iff {l : List Letter} :
    l ∈ caseSorted ↔
      l.SortedLE ∧ l.count w = 1 ∧ l.count x = 1 ∧ l.count y = 1 ∧ l.count z = 0 := by
  refine ⟨?_, fun ⟨hs, hw, hx, hy, hz⟩ ↦ ⟨l.count a, l.count b, l.count c, l.count d, ?_⟩⟩
  · rintro ⟨p, q, r, u, rfl⟩
    exact ⟨sortedLE_clause .., by simp [count_clause]⟩
  · refine (perm_iff_count.mpr fun ℓ ↦ ?_).eq_of_sortedLE hs (sortedLE_clause ..)
    cases ℓ <;> simp [count_clause, *]

theorem isRegular_caseSorted : caseSorted.IsRegular := by
  let D : Language Letter :=
    {l | l.SortedLE ∧ l.count w ≤ 1 ∧ l.count x ≤ 1 ∧ l.count y ≤ 1 ∧ l.count z = 0}
  have hD : D.IsSublistClosed := fun v l hvl ⟨hs, hw, hx, hy, hz⟩ ↦
    ⟨(hs.pairwise.sublist hvl).sortedLE, (hvl.count_le _).trans hw, (hvl.count_le _).trans hx,
      (hvl.count_le _).trans hy, Nat.le_zero.mp (hz ▸ hvl.count_le _)⟩
  have : caseSorted = D ⊓ (shuffleIdeal [w] ⊓ shuffleIdeal [x] ⊓ shuffleIdeal [y]) := by
    ext l
    change _ ↔ (_ ∧ _) ∧ ([w] <+ l ∧ [x] <+ l) ∧ [y] <+ l
    simp only [mem_caseSorted_iff, singleton_sublist, ← count_pos_iff]
    grind
  exact this ▸ hD.isRegular.inf
    (((isRegular_shuffleIdeal _).inf (isRegular_shuffleIdeal _)).inf (isRegular_shuffleIdeal _))

/-! ### The image of note 5 -/

/-- `eraseFrame` is the homomorphism of note 5, which erases `w`, `x` and `y`; it also erases `z`,
which does not occur in `r`. -/
def eraseFrame : Letter → List Letter
  | a => [a] | b => [b] | c => [c] | d => [d] | _ => []

theorem flatMap_eraseFrame_clause (p q r u : ℕ) : (clause p q r u).flatMap eraseFrame =
    replicate p a ++ replicate q b ++ replicate r c ++ replicate u d := by
  simp [clause, eraseFrame, flatMap_replicate]

theorem stringMap_eraseFrame_crossSerial :
    stringMap eraseFrame crossSerial = ambncmdn a b c d := by
  ext l
  constructor
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, (flatMap_eraseFrame_clause m n m n).symm⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m, n, rfl⟩, flatMap_eraseFrame_clause m n m n⟩

theorem not_isContextFree_crossSerial : ¬ crossSerial.IsContextFree := fun h ↦
  not_isContextFree_ambncmdn (by decide) (stringMap_eraseFrame_crossSerial ▸ h.stringMap eraseFrame)

/-! ### The claims and the argument -/

variable {W : Type*} {f : W → Letter} {L : Language W}

variable (f L) in
/-- `Claims f L` states the four claims of §3 about a language `L` over a vocabulary `W` whose
words `f` sends to letters. -/
structure Claims : Prop where
  /-- By Claims 1, 2 and 4, some clause `w aᵐ bⁿ x cᵐ dⁿ y` is grammatical for all `m`, `n`. -/
  exists_mem : ∀ m n, ∃ s ∈ L, s.map f = clause m n m n
  /-- By Claim 3, a clause of the schema has as many `c` (*laa*) as `a` (*d'chind*) and as many
  `d` (*hälfe*) as `b` (*em Hans*). -/
  count_eq : ∀ s ∈ L, s.map f ∈ schema →
    (s.map f).count a = (s.map f).count c ∧ (s.map f).count b = (s.map f).count d

/-- The image of a language meeting the claims, intersected with `r`, is `w aᵐ bⁿ x cᵐ dⁿ y`. -/
theorem Claims.map_inf_caseSorted (h : Claims f L) : L.map f ⊓ caseSorted = crossSerial := by
  ext l
  refine ⟨?_, fun ⟨m, n, hl⟩ ↦ ?_⟩
  · rintro ⟨⟨s, hs, rfl⟩, p, q, r, u, he⟩
    have := h.count_eq s hs (he ▸ clause_mem_schema p q r u)
    simp only [he, count_clause] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨p, q, he⟩
  · obtain ⟨s, hs, he⟩ := h.exists_mem m n
    exact ⟨⟨s, hs, he.trans hl.symm⟩, m, n, m, n, hl⟩

/-- A language meeting the four claims is not context-free. -/
theorem Claims.not_isContextFree (h : Claims f L) : ¬ L.IsContextFree := fun hL ↦
  not_isContextFree_crossSerial <|
    h.map_inf_caseSorted ▸ (hL.map f).inf_isRegular isRegular_caseSorted

/-- A language is not context-free if every clause `w aⁿ bⁿ x cⁿ dⁿ y` is grammatical and every
object noun phrase of a clause of the schema has a verb requiring its case, objects being
optional. -/
theorem not_isContextFree_of_count_le (hmem : ∀ n, ∃ s ∈ L, s.map f = clause n n n n)
    (hle : ∀ s ∈ L, s.map f ∈ schema →
      (s.map f).count a ≤ (s.map f).count c ∧ (s.map f).count b ≤ (s.map f).count d) :
    ¬ L.IsContextFree := fun hL ↦ by
  refine not_isContextFree_of_replicate_mem_of_count_le (by decide : [a, b, c, d].Nodup)
    (.of_forall fun n ↦ ?_) ?_
    (((hL.map f).inf_isRegular isRegular_caseSorted).stringMap eraseFrame)
  · obtain ⟨s, hs, he⟩ := hmem n
    exact ⟨clause n n n n, ⟨⟨s, hs, he⟩, n, n, n, n, rfl⟩, flatMap_eraseFrame_clause n n n n⟩
  · rintro _ ⟨_, ⟨⟨s, hs, rfl⟩, p, q, r, u, he⟩, rfl⟩
    have := hle s hs (he ▸ clause_mem_schema p q r u)
    simpa [he, count_clause, flatMap_eraseFrame_clause, count_replicate] using this

/-! ### The claims are consistent and not idle -/

/-- `countMatched` is the language of the words that meet Claim 3 if they are in the schema. -/
def countMatched : Language Letter :=
  {l | l ∈ schema → l.count a = l.count c ∧ l.count b = l.count d}

theorem claims_countMatched : Claims id countMatched where
  exists_mem m n := ⟨clause m n m n, fun _ ↦ by simp [count_clause], by simp⟩
  count_eq s hs hsch := by simpa using hs (by simpa using hsch)

/-- Claim 3 excludes the full language, which is context-free. -/
theorem not_claims_top : ¬ Claims id (⊤ : Language Letter) := fun h ↦ by
  simpa [count_clause] using
    h.count_eq (clause 1 0 0 0) trivial (by simpa using clause_mem_schema 1 0 0 0)

/-! ### The paper's clauses (1)–(22) -/

open German.Zurich.Verbs

/-- `npCase? np` is the case the article of the noun phrase `np` marks: a word article followed
by its noun, or a clitic article, written with a final apostrophe, attached to it. -/
def npCase? (np : String) : Option German.Zurich.Case :=
  let start (art : List Char) := if art.getLast? = some '\'' then art else art ++ [' ']
  (German.Zurich.articleCase.find? fun a ↦ start a.1.toList <+: np.toList).map (·.2)

/-- `objectCases e` lists the cases the articles of the clause `e` mark on its noun phrases. -/
def objectCases (e : Datum) : List German.Zurich.Case :=
  e.glossedTokens.filterMap (npCase? ·.1)

/-- `requiredCases e` lists the cases the verbs of the clause `e` require of their objects. -/
def requiredCases (e : Datum) : List German.Zurich.Case :=
  e.glossedTokens.flatMap fun t ↦ (verbs.find? (t.1 ∈ ·.forms)).elim [] (·.objects)

theorem length_objectCases_eq :
    ∀ e ∈ Examples.all, (objectCases e).length = (requiredCases e).length := by
  decide

/-- Among clauses (1)–(22), cross-serial or not, the acceptable ones are exactly those whose
objects bear the cases their verbs require, as many of each. -/
theorem acceptable_iff_perm :
    ∀ e ∈ Examples.all, e.judgment = .acceptable ↔ (objectCases e).Perm (requiredCases e) := by
  decide

end Shieber1985
