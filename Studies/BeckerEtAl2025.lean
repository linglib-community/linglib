module

public import Linglib.Phonology.Prosody.Grid
public import Mathlib.Data.List.TakeWhile
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Tactic.DeriveFintype

/-!
# The incoherent stress of Kuikuro

Formalization of [becker-etal-2025] (NLLT 43). Kuikuro builds iambic feet left to right with
final trochaic reversal; the last foot heads the word, and the primary stress is the head of the
head foot (p. 2365). The paper's title result is that the default High tone does not dock on
this syllable: a tone domain left-aligns to the primary stress of the phrase and expands
rightward up to (but not including) the next foot head — Culminativity-H ((7)), the paper's one
new constraint — so the High target can surface up to three syllables away from the stress it is
a correlate of (§7), dissociating the metrically most prominent syllable from the phonetically
salient one ([gordon-2016]'s incoherence, extended).

## Main definitions

* `fell`, `weFell`, `annatto` — words in isolation (Figs. 1–2, §1) as `Prosody.Tree`s;
  `annattoFell` — the two-word phrase of Fig. 3, with the noun as phrase-head word.
* `toneDomainTail`, `toneTarget` — rightward-maximal tone-domain expansion over a grid: the run
  of unstressed columns after the phrase head, capped before the next foot head and the
  phrase-final syllable ((4)–(7)).

## Main results

* `footing_optimal` — trochaic reversal is OT-optimal under `*V:]φ ≫ Parse-σ ≫ Iamb` ((1)–(3),
  Table 2).
* `isHeaded_*`, `headTerminals_*` — each word's primary stress is its unique head terminal
  (metrical culminativity, [hyman-2006]).
* `toneDomainTail_unstressed` — expansion never admits a stressed syllable: the
  Culminativity-H of ((7)) holds of every predicted domain by construction.
* `tone_coherent_in_isolation`, `stress_tone_incoherence` — in isolation the High target is the
  head terminal itself; in the phrase it is a height-1 syllable three to the right of the peak,
  blocked by the next foot head.

Deferred alongside lexical tone (§5): lexical long vowels (Max-μ, Tables 3–4), word minimality
(§3.5), final shortening (§4.1), and the generality of initial-vowel unparsing (§4.3). Weights:
`1` = short σ, `2` = long σ (iambic lengthening); a foot's `isHead` σ is its head, and the head
foot/word carries `isHead := true`.

## References

* [becker-etal-2025] — the paper.
* [liberman-prince-1977], [hayes-1995], [prince-smolensky-1993] — the grid, foot typology, and
  violable-constraint machinery.
* [gordon-2016] — incoherent stress; [hyman-2006] — culminativity.
-/

@[expose] public section

namespace BeckerEtAl2025

open Prosody OptimalityTheory

/-! ### Words in isolation ([becker-etal-2025] §3) -/

/-- *[(ala:)(makí:)lɨ]* 's/he fell' ([becker-etal-2025] Fig. 1): two iambs and a stray final σ.
    The rightmost foot heads the word, so the long [kí:] is the primary stress. -/
def fell : Tree :=
  .om
    [ .ft false [.σ 1 false, .σ 2 true],
      .ft true  [.σ 1 false, .σ 2 true],
      .σ 1 false ]

/-- *[(tsiha:)(lama:)(kílɨ)]* 'we fell' ([becker-etal-2025] Fig. 2): even parity, so the final
    two short syllables reverse to a **trochee** — the head foot — whose initial [kí] is the
    primary stress. -/
def weFell : Tree :=
  .om
    [ .ft false [.σ 1 false, .σ 2 true],
      .ft false [.σ 1 false, .σ 2 true],
      .ft true  [.σ 1 true, .σ 1 false] ]

/-- *[(umí:)ŋi]* 'annatto' ([becker-etal-2025] §1, p. 2365): one iamb and a stray final σ; the
    long [mí:] is the primary stress. -/
def annatto : Tree :=
  .om
    [ .ft true [.σ 1 false, .σ 2 true],
      .σ 1 false ]

/-! ### The grid: secondary stress on every foot head, primary on the head foot's

Reading `Tree.columns ∘` the footing recovers the stress profile: `1` unstressed, `2` a secondary
(a non-head foot's head), `3` the primary (the head foot's head). -/

theorem gridColumns_fell    : Tree.columns fell    = [1, 2, 1, 3, 1] := by decide
theorem gridColumns_weFell  : Tree.columns weFell  = [1, 2, 1, 2, 3, 1] := by decide
theorem gridColumns_annatto : Tree.columns annatto = [1, 3, 1] := by decide

/-! ### Primary stress is the head terminal ([becker-etal-2025] p. 2365)

Each word has a **unique head terminal** (`Tree.IsHeaded` — metrical culminativity, Liberman &
Prince's
head-terminal uniqueness; cf. [hyman-2006]), and it is exactly the head syllable of the head foot —
the long
`kí:`/`mí:`, or the reversed-trochee's initial `kí`. The primary stress is read off the grid's live
column as an *element*. -/

theorem isHeaded_fell    : Tree.IsHeaded fell    := by decide
theorem isHeaded_weFell  : Tree.IsHeaded weFell  := by decide
theorem isHeaded_annatto : Tree.IsHeaded annatto := by decide

/-- 's/he fell': the head terminal is the long `kí:` (head of the rightmost iamb). -/
theorem headTerminals_fell : Tree.headTerminals fell = [.σ 2 true] := by decide

/-- 'we fell': the head terminal is the reversed trochee's initial short `kí`. -/
theorem headTerminals_weFell : Tree.headTerminals weFell = [.σ 1 true] := by decide

/-- 'annatto': the head terminal is the long `mí:`. -/
theorem headTerminals_annatto : Tree.headTerminals annatto = [.σ 2 true] := by decide

/-- The same fact **declaratively** ([liberman-prince-1977]): `kí:` is the head terminal of `fell`
    — reached from ω by an all-head descent (ω → head foot → head σ), `Tree.IsHeadTerminal` — lifted
    from the computed list by `Tree.headTerminal_sound`, not just by computing the list. -/
theorem isHeadTerminal_fell : Tree.IsHeadTerminal fell (.σ 2 true) :=
  Tree.headTerminal_sound (by decide)

/-! ### The trochaic reversal is OT-optimal ([becker-etal-2025] §3.1, Table 2)

Why the final foot reverses to a trochee: an even-parity `/σσσσ/` parsed as two iambs leaves a
**phrase-final long vowel** (`*V:]φ`); leaving the last two σ unparsed violates `Parse-σ`; so they
parse as a trochee, violating only the low-ranked `Iamb`. Ranking `*V:]φ ≫ Parse-σ ≫ Iamb`
([becker-etal-2025] (1)–(3), Table 2). -/

/-- The three footings of `/σσσσ/` weighed in [becker-etal-2025]'s Table 2. -/
inductive FootingCand where
  /-- `(σ́σ:)(σ́σ:)` — two iambs; a final long vowel. -/
  | twoIambs
  /-- `(σ́σ:)σσ` — one iamb, the last two σ unparsed. -/
  | iambStrays
  /-- `(σ́σ:)(´σσ)` — an iamb and a final **trochee** (the optimum). -/
  | iambTrochee
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Each candidate as a footed tree (rightmost foot the head). -/
def FootingCand.toTree : FootingCand → Tree
  | .twoIambs    => .om [ .ft false [.σ 1 false, .σ 2 true],
                                .ft true  [.σ 1 false, .σ 2 true] ]
  | .iambStrays  => .om [ .ft true  [.σ 1 false, .σ 2 true],
                                .σ 1 false, .σ 1 false ]
  | .iambTrochee => .om [ .ft false [.σ 1 false, .σ 2 true],
                                .ft true  [.σ 1 true, .σ 1 false] ]

/-- **Parse-σ** ([becker-etal-2025] (1)): one mark per unparsed (stray) σ — a σ-leaf under ω. -/
def cParse : Constraint FootingCand := fun c => match c.toTree with
  | .node _ cs => (cs.filter (fun d => d.value.level = .syl)).length

/-- **Iamb** ([becker-etal-2025] (2)): one mark per foot that is not right-headed (head σ ≠ final).
    -/
def cIamb : Constraint FootingCand := fun c => match c.toTree with
  | .node _ cs => (cs.filter (fun d => match d with
      | .node a ds => decide (a.level = .ft) && !((ds.getLast?.map (·.value.isHead)).getD false))).length

/-- **`*V:]φ`** ([becker-etal-2025] (3)): one mark for a long vowel in the **phrase**-final σ (for a
    one-word phrase, the word-final σ). -/
def cStarV : Constraint FootingCand := fun c =>
  match (Tree.terminals c.toTree).getLast? with
  | some leaf => if decide (leaf.value.weight? = some 2) then 1 else 0
  | none      => 0

def candidates : List FootingCand := [.twoIambs, .iambStrays, .iambTrochee]

/-- The ranking `*V:]φ ≫ Parse-σ ≫ Iamb` ([becker-etal-2025] Table 2). -/
def footingRanking : List (Constraint FootingCand) := [cStarV, cParse, cIamb]

/-- The violation profiles ([becker-etal-2025] Table 2):

    | candidate     | `*V:]φ` | Parse-σ | Iamb |
    |----------------|---------|---------|------|
    | (σ́σ:)(σ́σ:)     |   1*    |   0     |  0   |
    | (σ́σ:)σσ        |   0     |   2*    |  0   |
    | ☞ (σ́σ:)(´σσ)   |   0     |   0     |  1   |

    `Max-μ` — which governs lexical long vowels (Tables 4 and 6; ranked below `*V:]φ` and above
    `Parse-σ`) — plays no role among these all-short candidates and is omitted. -/
theorem starV_violations : candidates.map cStarV = [1, 0, 0] := by decide
theorem parse_violations : candidates.map cParse = [0, 2, 0] := by decide
theorem iamb_violations  : candidates.map cIamb  = [0, 0, 1] := by decide

/-- **The trochaic reversal wins** ([becker-etal-2025] Table 2): under `*V:]φ ≫ Parse-σ ≫ Iamb` the
    optimal footing of `/σσσσ/` is the iamb + final **trochee** — no final long vowel, no unparsed
    σ, at the cost of one (low-ranked) non-right-headed foot. -/
theorem footing_optimal :
    (Tableau.ofList Finset.univ footingRanking).optimal = {.iambTrochee} := by decide

/-! ### The tone domain and Culminativity-H ([becker-etal-2025] §4.2)

A phrase carries one High tone. Its domain left-aligns to the primary stress of the phrase
((4)), expands rightward maximally ((5)), excludes the phrase-final syllable ((6)), and stops
before the next foot head — Culminativity-H ((7)): at most one foot head per domain. Over a
grid, expansion takes the run of height-`1` columns after the head column; the High target is
the domain's last syllable. -/

/-- The heights of the syllables a tone domain expands over: the unstressed (height-`1`) run
    after the phrase-head column, capped before the phrase-final syllable ((5)–(7)). -/
def toneDomainTail (cols : Grid) (head : ℕ) : Grid :=
  (cols.dropLast.drop (head + 1)).takeWhile (· ≤ 1)

/-- The High-tone target: the last syllable of the maximally expanded domain. -/
def toneTarget (cols : Grid) (head : ℕ) : ℕ :=
  head + (toneDomainTail cols head).length

/-- Culminativity-H holds of every predicted domain by construction: expansion never admits a
    stressed syllable, so no domain contains a second foot head ((7)). -/
theorem toneDomainTail_unstressed (cols : Grid) (head : ℕ) :
    ∀ h ∈ toneDomainTail cols head, h ≤ 1 := fun _ hh => by
  simpa using List.mem_takeWhile_imp hh

/-- In isolation the tone is coherent: the domain cannot expand — the phrase-final cap ((6))
    closes it at the head — so the High target is the head terminal itself, the default
    penultimate tone of §3. Head indices are visible in `gridColumns_*` above. -/
theorem tone_coherent_in_isolation :
    toneTarget (Tree.columns fell) 3 = 3 ∧ toneTarget (Tree.columns weFell) 4 = 4 ∧
      toneTarget (Tree.columns annatto) 1 = 1 := by
  decide

/-- Each word's grid is culminative: exactly one peak column, the head terminal's. -/
theorem isCulminative_words :
    Grid.IsCulminative (Tree.columns fell) ∧ Grid.IsCulminative (Tree.columns weFell) ∧
      Grid.IsCulminative (Tree.columns annatto) := by
  decide

/-- The two-word phrase *[(umɨ:)ŋi ⟨a⟩(láma:)(kilɨ)]* 'the annatto fell' (Fig. 3): the noun is
    the phrase-head word, and the verb refoots in phrasal position — initial vowel unparsed
    (§4.3), one iamb, and a final trochee. -/
def annattoFell : Tree :=
  .ph [ RoseTree.node (.om true) [Tree.ft true [.σ 1 false, .σ 2 true], Tree.σ 1 false],
        .om [ .σ 1 false,
              .ft false [.σ 1 false, .σ 2 true],
              .ft true [.σ 1 true, .σ 1 false] ] ]

/-- The phrase grid: the noun's head terminal is promoted to the phrase peak (height 4). -/
theorem gridColumns_annattoFell :
    Tree.columns annattoFell = [1, 4, 1, 1, 1, 2, 3, 1] := by decide

/-- The phrase is headed, culminatively, by the noun's long [mɨ:]. -/
theorem annattoFell_headed :
    Tree.IsHeaded annattoFell ∧ Grid.IsCulminative (Tree.columns annattoFell) := by decide

/-- **The incoherence** (§1, §7): from the phrase peak (index 1), the tone domain expands over
    three unstressed syllables and targets index 4 — the height-1 [lá] — while expansion is
    blocked by the next foot head [ma:] (index 5, height 2). The metrically most prominent
    syllable and the High-toned phonetically salient one come apart. -/
theorem stress_tone_incoherence :
    toneTarget (Tree.columns annattoFell) 1 = 4 ∧
      (Tree.columns annattoFell).getD 4 0 = 1 ∧
        (Tree.columns annattoFell).getD 5 0 = 2 := by
  decide

end BeckerEtAl2025
