module

public import Linglib.Syntax.Cat
public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.WordOrder
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Hawkins (1994): A Performance Theory of Order and Constituency

The parser builds a phrasal mother as soon as it meets a word whose category determines it. A
mother's constituent recognition domain runs from the word constructing its first immediate
constituent to the word constructing its last, and Early Immediate Constituents prefers orders
whose domains recognize the constituents in the fewest words. A domain read right to left [keeps
its words in reverse order](##crd_mirror), so [the ratio of constituents to words cannot tell an
order from its mirror image](##icToWord_mirror), while [the left-to-right ratio can](##ratios_5_3).
Of a head over a phrase whose head has a complement, [the consistent orders score best, and the
head kept leftmost beats the phrase kept leftmost](##leftToRight_binary_lt).

## Implementation notes

* A constituent enters a domain as the words before and after its constructing word (`IC`).
  Phrase-structure trees over `PhraseStructure.Cat` give these numbers through Mother Node
  Construction (`toIC`), with the constructing categories of p. 61; the schematic orders of
  (3.16), printed as category strings, enter as constituents directly.
* Ratios are exact rationals; the book prints them as rounded percentages.
* The ratio of constituents to non-terminal nodes is not formalized: the book uses the ratio to
  words as its shorthand (p. 75).

## References

* [hawkins-1994]
-/

@[expose] public section

namespace Hawkins1994

open PhraseStructure

/-! ### Constituent recognition domains -/

/-- An immediate constituent of a mother, as its recognition domain reads it: the words of the
constituent before and after the word that constructs it. -/
@[ext]
structure IC where
  /-- The words before the constructing word. -/
  pre : ℕ
  /-- The words after the constructing word. -/
  post : ℕ
  deriving DecidableEq, Repr

namespace IC

/-- The words of a constituent. -/
def words (c : IC) : ℕ := c.pre + 1 + c.post

/-- A constituent read right to left. -/
def mirror (c : IC) : IC := ⟨c.post, c.pre⟩

@[simp] theorem pre_mirror (c : IC) : c.mirror.pre = c.post := rfl

@[simp] theorem post_mirror (c : IC) : c.mirror.post = c.pre := rfl

@[simp] theorem words_mirror (c : IC) : c.mirror.words = c.words := by
  simp only [words, pre_mirror, post_mirror]; omega

end IC

/-- The constituents of a mother read right to left. -/
def mirror (l : List IC) : List IC := (l.map IC.mirror).reverse

@[simp] theorem length_mirror (l : List IC) : (mirror l).length = l.length := by simp [mirror]

/-- The words each constituent after the first contributes to the recognition domain: all its
words, but for the last only those up to its constructing word. -/
def crdTail : List IC → List ℕ
  | [] => []
  | [c] => [c.pre + 1]
  | c :: d :: l => c.words :: crdTail (d :: l)

/-- (3.2) The words each constituent contributes to the constituent recognition domain, which runs
from the word constructing the first constituent to the word constructing the last. -/
def crd : List IC → List ℕ
  | [] => []
  | [_] => [1]
  | c :: d :: l => (c.post + 1) :: crdTail (d :: l)

/-- (3.13) The ratio of immediate constituents to the words of the recognition domain. -/
def icToWord (l : List IC) : ℚ := l.length / (crd l).sum

/-- (3.15) The left-to-right ratio: the `i`-th constituent scores `i` over the words of the domain
up to the last of them it dominates, and the domain scores the mean. -/
def leftToRight (l : List IC) : ℚ :=
  ((List.range l.length).map fun (i : ℕ) ↦
    ((i : ℚ) + 1) / (((crd l).take (i + 1)).sum : ℚ)).sum / l.length

private theorem crdTail_concat (l : List IC) (c : IC) :
    crdTail (l ++ [c]) = l.map IC.words ++ [c.pre + 1] := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    cases l with
    | nil => rfl
    | cons e l => simp only [List.cons_append, crdTail] at ih ⊢; rw [ih]; rfl

private theorem crd_cons_concat (c d : IC) (l : List IC) :
    crd (c :: (l ++ [d])) = (c.post + 1) :: (l.map IC.words ++ [d.pre + 1]) := by
  cases l with
  | nil => rfl
  | cons e l => rw [List.cons_append, crd, ← List.cons_append, crdTail_concat]

/-- A recognition domain read right to left contributes its words in reverse order. -/
theorem crd_mirror (l : List IC) : crd (mirror l) = (crd l).reverse := by
  rcases l with _ | ⟨c, l⟩
  · rfl
  rcases l.eq_nil_or_concat with rfl | ⟨l, d, rfl⟩
  · rfl
  rw [List.concat_eq_append]
  have : mirror (c :: (l ++ [d])) = d.mirror :: ((mirror l) ++ [c.mirror]) := by
    simp [mirror]
  rw [this, crd_cons_concat, crd_cons_concat]
  simp [mirror, List.map_reverse, Function.comp_def]

-- (3.13) is blind to the direction of reading
theorem icToWord_mirror (l : List IC) : icToWord (mirror l) = icToWord l := by
  simp only [icToWord, length_mirror, crd_mirror, List.sum_reverse]

/-! ### Mother Node Construction -/

/-- The pairs of a word's category and the category of the mother it constructs (p. 61):
determiners and nouns construct noun phrases, verbs verb phrases, adpositions adpositional
phrases, adjectives adjective phrases, complementizers the clause they introduce and auxiliaries
the clause. -/
def constructing : Finset (Cat × Cat) :=
  {(.Det, .N), (.N, .N), (.V, .V), (.P, .P), (.Adj, .Adj), (.C, .C), (.Aux, .S)}

-- (3.6) MNCC Uniqueness: a constructing category constructs one mother
theorem constructing_unique :
    ∀ p ∈ constructing, ∀ q ∈ constructing, p.1 = q.1 → p.2 = q.2 := by
  decide

variable {W : Type*}

/-- A daughter is a word whose category constructs a mother of category `c`. -/
def Constructs (c : Cat) (t : PhraseStructure.Tree Cat W) : Prop :=
  ∃ x ∈ t.value.terminal?, (x.1, c) ∈ constructing

instance (c : Cat) (t : PhraseStructure.Tree Cat W) : Decidable (Constructs c t) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

/-- (3.3) Mother Node Construction: a constituent enters its mother's domain at the first of its
daughter words whose category constructs it, a word at itself. -/
def toIC : PhraseStructure.Tree Cat W → Option IC
  | RoseTree.node (.terminal _ _) [] => some ⟨0, 0⟩
  | RoseTree.node (.phrase c _) ds =>
    (ds.findIdx? (decide <| Constructs c ·)).map fun j ↦
      ⟨((ds.take j).map fun d ↦ (Tree.yield d).length).sum,
        ((ds.drop (j + 1)).map fun d ↦ (Tree.yield d).length).sum⟩
  | _ => none

/-- The immediate constituents of a mother, as its recognition domain reads them. -/
def ics (t : PhraseStructure.Tree Cat W) : Option (List IC) := t.children.mapM toIC

/-! ### The left-to-right ratio -/

theorem leftToRight_pair (x y : IC) :
    leftToRight [x, y] = (1 / (x.post + 1) + 2 / (x.post + 1 + (y.pre + 1))) / 2 := by
  norm_num [leftToRight, crd, crdTail, List.range_succ]

/-- (3.16'): of three noun-phrase domains of six words with a four-word clause, the order with the
single-word constituents first scores 83.3%, the clause between them 63.3%, and the clause first
38.3%. -/
theorem leftToRight_3_16 :
    leftToRight [⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩] = 5 / 6 ∧ leftToRight [⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩] = 19 / 30 ∧
      leftToRight [⟨0, 3⟩, ⟨0, 0⟩, ⟨0, 0⟩] = 23 / 60 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [leftToRight, crd, crdTail, IC.words, List.range_succ]

/-! ### A head over a phrase, (3.22) -/

/-- A phrase whose head has a complement of `m` words, the head in direction `d`. -/
def phrase : HeadDirection → ℕ → IC
  | .headInitial, m => ⟨0, m⟩
  | .headFinal, m => ⟨m, 0⟩

/-- (3.22) The constituents of a head over a phrase whose head has a complement of `m` words, the
two heads in directions `top` and `bottom`: `[V [P NP]]` for two head-initial heads. -/
def binary (top bottom : HeadDirection) (m : ℕ) : List IC :=
  match top with
  | .headInitial => [⟨0, 0⟩, phrase bottom m]
  | .headFinal => [phrase bottom m, ⟨0, 0⟩]

-- (3.21): the four orders of a head over a phrase come in mirror pairs
theorem binary_swap (top bottom : HeadDirection) (m : ℕ) :
    binary top.swap bottom.swap m = mirror (binary top bottom m) := by
  cases top <;> cases bottom <;> rfl

theorem binary_zero (top bottom : HeadDirection) : binary top bottom 0 = [⟨0, 0⟩, ⟨0, 0⟩] := by
  cases top <;> cases bottom <;> rfl

theorem leftToRight_binary_consistent (d : HeadDirection) (m : ℕ) :
    leftToRight (binary d d m) = 1 := by
  cases d <;> rw [binary, phrase, leftToRight_pair] <;> norm_num

theorem leftToRight_initial_final (m : ℕ) :
    leftToRight (binary .headInitial .headFinal m) = (1 + 2 / (m + 2)) / 2 := by
  rw [binary, phrase, leftToRight_pair]; push_cast; ring

theorem leftToRight_final_initial (m : ℕ) :
    leftToRight (binary .headFinal .headInitial m) = (1 / (m + 1) + 2 / (m + 2)) / 2 := by
  rw [binary, phrase, leftToRight_pair]; push_cast; ring

/-- (3.22), pp. 96–97 and 254: when the lower head has a complement, the two consistent orders of
a head over a phrase score 100%, the head kept leftmost `[C IC]` scores less, and the phrase kept
leftmost `[IC C]` less still. -/
theorem leftToRight_binary_lt {m : ℕ} (hm : 0 < m) (d : HeadDirection) :
    leftToRight (binary .headFinal .headInitial m) <
        leftToRight (binary .headInitial .headFinal m) ∧
      leftToRight (binary .headInitial .headFinal m) < leftToRight (binary d d m) ∧
      leftToRight (binary d d m) = 1 := by
  rw [leftToRight_initial_final, leftToRight_final_initial, leftToRight_binary_consistent]
  have hm : (0 : ℚ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_, rfl⟩
  · rw [div_lt_div_iff_of_pos_right two_pos, add_lt_add_iff_right,
      div_lt_one (by positivity)]
    linarith
  · rw [div_lt_one two_pos, ← lt_sub_iff_add_lt', div_lt_iff₀ (by positivity)]
    linarith

/-! ### (5.3) and (5.4) -/

section Examples

open PhraseStructure.Tree (node terminal)

/-- (5.3): *played the friends with*, the verb before a postpositional phrase. -/
def ex5_3 : PhraseStructure.Tree Cat String :=
  node .V [terminal .V "played",
    node .P [node .N [terminal .Det "the", terminal .N "friends"], terminal .P "with"]]

/-- (5.4): *with the friends played*, a prepositional phrase before the verb. -/
def ex5_4 : PhraseStructure.Tree Cat String :=
  node .V [node .P [terminal .P "with", node .N [terminal .Det "the", terminal .N "friends"]],
    terminal .V "played"]

/-- (5.3'), (5.4'), p. 255: the domains of (5.3) and (5.4) are mirror images of each other; both
recognize two constituents in four words, 50%, but read left to right (5.3) scores 75% and
(5.4) 42%. -/
theorem ratios_5_3 :
    ics ex5_3 = some (binary .headInitial .headFinal 2) ∧
      ics ex5_4 = some (mirror (binary .headInitial .headFinal 2)) ∧
      icToWord (binary .headInitial .headFinal 2) = 1 / 2 ∧
      icToWord (mirror (binary .headInitial .headFinal 2)) = 1 / 2 ∧
      leftToRight (binary .headInitial .headFinal 2) = 3 / 4 ∧
      leftToRight (mirror (binary .headInitial .headFinal 2)) = 5 / 12 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_⟩
  · norm_num [icToWord, binary, phrase, crd, crdTail]
  · rw [icToWord_mirror]; norm_num [icToWord, binary, phrase, crd, crdTail]
  · rw [leftToRight_initial_final]; norm_num
  · rw [← binary_swap, HeadDirection.swap_headInitial, HeadDirection.swap_headFinal,
      leftToRight_final_initial]
    norm_num

end Examples

end Hawkins1994
