module

public import Linglib.Data.Examples.Borer2013
public import Linglib.Syntax.Minimalist.Category.FunctionalSequence
public import Studies.Embick2010

/-!
# Borer (2013): Structuring Sense: Volume III: Taking Form

A category-less root takes its category from the extended projection above it, so *dance* is a noun
under a determiner and a verb under infinitival *to*, with nothing added to it. Such roots never
occur as adjectives (*too dance*), and the words that occur as adjectives occur neither as nouns nor
as verbs (*a green*, *to green*). Distributed Morphology categorizes a root by a head *n*, *v* or
*a* that may be null, so it has to rule each pairing of a root with a head in or out. Borer's
resolution is that adjectives are not roots. Like derivatives they are born categorized, and a
categorized core fits only the extended projection of its own category, while the adjectival
extended projection cannot categorize a root.

A root also selects the realization of what attaches to it, as *run* selects its past *ran* and
*goose* its plural *geese*. Selection is local, so only what attaches to a bare root can be
selected: derivatives inflect regularly, and on the resolution so do adjectives. Distributed
Morphology puts a head between every stem and its inflection, and recovers local selection only by
letting null heads be transparent. The chapter ends on a problem it leaves open: *-ify* and *en-*
are selected by the roots of *clarify* and *enlarge*, so a functor taking adjectives attaches to a
bare root after all.

## Main statements

* `licenses_nominal_and_verbal_iff`: roots, and roots alone, occur both as nouns and as verbs,
  which with the lexicon derives every judgment of the paradigm (`acceptable_iff_licensed`).
* `complement_ne_none_of_wellFormed`: nothing that takes an adjective attaches to a bare root, so
  no root selects its realization.
* `not_exists_licensing`: no condition on the category of a complement both derives the paradigm
  and lets the verbalizers of *clarify* and *enlarge* take their roots.
* `dm_seesRoot`: in Distributed Morphology's representations no inflection sees its root unless
  null heads are transparent.

## Implementation notes

* The category of a core is an `Option CatFamily`, `none` for a root, and an example's frame is
  the family of the extended projection it builds: nominal under *a* and *the*, verbal under *to*,
  adjectival under *too*. The adpositional extended projection is taken not to categorize roots,
  which the paradigm does not test.
* The verbal *thin* and *yellow* are listed as categorized verbs, since as roots they would be
  nouns as well.
* A word's terminals are the book's categorial functors, with the category each projects and the
  categories it takes, the segments of extended projections, among them the comparative and the
  superlative, and the head an adjective is born with. Which realizations a root selects is taken
  from the book's table of functors and its discussion of *-en* and *en-*.
* Distributed Morphology's words are read with the heads, cycles and ∅-Transparency of
  `Embick2010`.

## TODO

The table of functors is not recorded as data, only the choices of the words built with them, and
the functors with a meaning of their own (*-ing*, *-er*, *-ship*), which the book sets apart from
the default-and-selection pattern, are treated as functors like the rest. The book's arguments
from stacked null heads, which nothing rules out once null heads are transparent, and from the
direction of derivation in Kiparsky's examples, are not formalized; they are where Embick's cycles
and contextual categorization would come apart.

## References

* [borer-2013]
* [embick-2010]
-/

@[expose] public section

namespace Borer2013

open Minimalist

/-! ### Categorization by the extended projection -/

/-- `Licenses e κ` says that the extended projection of family `e` takes a core of category `κ`,
where `none` is a category-less root. A categorized core fits only the extended projection of its
own category, and a root becomes a noun or a verb in its extended projection, but the adjectival
one cannot make it an adjective. -/
def Licenses (e : CatFamily) : Option CatFamily → Prop
  | some c => c = e
  | none => e = .nominal ∨ e = .verbal

instance (e : CatFamily) : DecidablePred (Licenses e)
  | some c => inferInstanceAs (Decidable (c = e))
  | none => inferInstanceAs (Decidable (e = .nominal ∨ e = .verbal))

variable {e : CatFamily} {κ : Option CatFamily}

@[simp] theorem licenses_some {c : CatFamily} : Licenses e (some c) ↔ c = e := Iff.rfl

@[simp] theorem licenses_none : Licenses e none ↔ e = .nominal ∨ e = .verbal := Iff.rfl

/-- Roots, and roots alone, occur both as nouns and as verbs. -/
theorem licenses_nominal_and_verbal_iff :
    Licenses .nominal κ ∧ Licenses .verbal κ ↔ κ = none := by
  cases κ <;> grind [Licenses]

theorem Licenses.eq_adjectival (hA : Licenses .adjectival κ) (h : Licenses e κ) :
    e = .adjectival := by
  cases κ <;> simp_all

/-- A word that is both a verb and an adjective is listed under two categories, since no core is
licensed in both extended projections. The verbal uses of *thin* and *yellow* cannot be predicted
from their adjectival ones and must be listed (fn. 39). -/
theorem exists_ne_of_verbal_of_adjectival {l : List (Option CatFamily)}
    (hV : ∃ κ ∈ l, Licenses .verbal κ) (hA : ∃ κ ∈ l, Licenses .adjectival κ) :
    ∃ κ ∈ l, ∃ κ' ∈ l, κ ≠ κ' := by
  obtain ⟨κ, hκ, hV⟩ := hV
  obtain ⟨κ', hκ', hA⟩ := hA
  exact ⟨κ, hκ, κ', hκ', by rintro rfl; cases hA.eq_adjectival hV⟩

/-! ### The paradigm -/

/-- The words of the paradigm, each with the category of a core it is listed as. The roots are
category-less, the adjectives are born categorized, and *thin* and *yellow* are listed again as
verbs. -/
def lexicon : List (String × Option CatFamily) :=
  [("dance", none), ("jump", none), ("walk", none), ("table", none), ("chair", none),
    ("wardrobe", none), ("question", none), ("mean", some .adjectival),
    ("green", some .adjectival), ("fat", some .adjectival), ("tall", some .adjectival),
    ("smart", some .adjectival), ("wide", some .adjectival), ("big", some .adjectival),
    ("thin", some .adjectival), ("thin", some .verbal), ("yellow", some .adjectival),
    ("yellow", some .verbal)]

/-- The categories a word is listed under. -/
def categories (w : String) : List (Option CatFamily) :=
  lexicon.filterMap fun p ↦ if p.1 = w then some p.2 else none

/-- A row records the extended projection an example puts its word in, the categories of the
cores the word is listed as, and the judgment. -/
structure Row where
  frame : CatFamily
  cores : List (Option CatFamily)
  judgment : Judgment
  deriving DecidableEq

/-- The row of an example whose word is listed. -/
def Row.ofDatum (d : Datum) : Option Row := do
  let frame ← d.parse? "frame"
    [("nominal", CatFamily.nominal), ("verbal", .verbal), ("adjectival", .adjectival)]
  let cats := categories (← d.feature? "item")
  guard (cats ≠ [])
  pure ⟨frame, cats, d.judgment⟩

/-- The examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

/-- An example is acceptable exactly when its word is listed as a core that fits the extended
projection the example puts it in: *a dance*, *to dance* and *too green* are acceptable, and
*too dance*, *a green* and *to green* are not. -/
theorem acceptable_iff_licensed :
    ∀ d ∈ data, d.judgment = .acceptable ↔ ∃ κ ∈ d.cores, Licenses d.frame κ := by
  decide +kernel

/-! ### Local selection -/

/-- A terminal of a word above its root is a categorial functor, projecting a category over a
complement of one of the categories it takes, a segment of an extended projection, or the head
that an item is born with. -/
inductive Terminal
  | functor (proj : CatFamily) (takes : List CatFamily)
  | segment (e : CatFamily)
  | born (c : CatFamily)
  deriving DecidableEq, Repr

/-- The category a terminal projects. -/
def Terminal.proj : Terminal → CatFamily
  | .functor p _ | .segment p | .born p => p

/-- The category of what the terminal at position `i` attaches to, the bare root for the first
terminal and otherwise the category of the terminal below. -/
def complement (ts : List Terminal) : ℕ → Option CatFamily
  | 0 => none
  | i + 1 => ts[i]?.map Terminal.proj

/-- A terminal takes a complement of category `κ` under the licensing `L` when it is a functor
and `L` licenses `κ` in one of the categories it takes, a segment whose extended projection `L`
licenses `κ` in, or a born head on its root. -/
def Terminal.Takes (L : CatFamily → Option CatFamily → Prop) : Terminal → Option CatFamily → Prop
  | .functor _ cs, κ => ∃ c ∈ cs, L c κ
  | .segment e, κ => L e κ
  | .born _, κ => κ = none

instance (t : Terminal) (κ : Option CatFamily) : Decidable (t.Takes Licenses κ) :=
  match t with
  | .functor _ cs => inferInstanceAs (Decidable (∃ c ∈ cs, Licenses c κ))
  | .segment e => inferInstanceAs (Decidable (Licenses e κ))
  | .born _ => inferInstanceAs (Decidable (κ = none))

/-- A word is well formed under `L` when each of its terminals takes what it attaches to. -/
def WellFormed (L : CatFamily → Option CatFamily → Prop) (ts : List Terminal) : Prop :=
  ∀ i (h : i < ts.length), ts[i].Takes L (complement ts i)

instance (ts : List Terminal) : Decidable (WellFormed Licenses ts) :=
  Nat.decidableBallLT _ _

/-- Whether a terminal has its default realization or one that its root selects. -/
inductive Choice
  | default
  | rootSelected
  deriving DecidableEq, Repr

/-- A word records its terminals, innermost first, the terminal whose realization is at issue,
and the choice of that realization. -/
structure Word where
  terminals : List Terminal
  target : ℕ
  choice : Choice
  deriving DecidableEq, Repr

/-- The terminals as named in the rows. -/
def terminalTable : List (String × Terminal) :=
  [("T-PST", .segment .verbal), ("CL-PL", .segment .nominal), ("CMPR", .segment .adjectival),
    ("SUPL", .segment .adjectival), ("CV[N]", .functor .verbal [.nominal]),
    ("CV[A]", .functor .verbal [.adjectival]),
    ("CV[A/N]", .functor .verbal [.adjectival, .nominal]), ("CN[V]", .functor .nominal [.verbal]),
    ("CN[N]", .functor .nominal [.nominal]), ("CN[A]", .functor .nominal [.adjectival]),
    ("ING", .functor .nominal [.verbal]), ("SHIP", .functor .nominal [.nominal]),
    ("ER", .functor .nominal [.verbal]), ("A", .born .adjectival)]

/-- The choices as named in the rows. -/
def choiceTable : List (String × Choice) := [("default", .default), ("rootSelected", .rootSelected)]

/-- The word of an example in the book's own representation, its target counted from one. -/
def Word.ofDatum (d : Datum) : Option Word := do
  guard (d.feature? "representation" = some "xsm")
  let ts ← ["h1", "h2", "h3"].filterMap (d.feature? ·) |>.mapM (terminalTable.lookup ·)
  let t ← d.nat? "target"
  guard (0 < t ∧ t ≤ ts.length)
  pure ⟨ts, t - 1, ← d.parse? "choice" choiceTable⟩

/-- The words of the chapter's structures. -/
def words : List Word := Examples.all.filterMap Word.ofDatum

/-- A word as Distributed Morphology represents it, with the inflection whose realization is at
issue. -/
structure DMWord where
  spine : DistributedMorphology.ComplexHead DistributedMorphology.Root Embick2010.Morpheme
  target : Fin spine.heads.length
  choice : Choice

/-- The word of an example in Distributed Morphology's representation. -/
def DMWord.ofDatum (d : Datum) : Option DMWord := do
  guard (d.feature? "representation" = some "dm")
  let hs := Embick2010.heads d
  let t ← d.nat? "target"
  let c ← d.parse? "choice" choiceTable
  if h : t - 1 < hs.length then pure ⟨⟨⟨0⟩, hs⟩, ⟨t - 1, h⟩, c⟩ else none

/-- The words of the renderings of Distributed Morphology. -/
def dmWords : List DMWord := Examples.all.filterMap DMWord.ofDatum

theorem isSome_ofDatum : ∀ d ∈ Examples.all,
    (Row.ofDatum d).isSome || (Word.ofDatum d).isSome || (DMWord.ofDatum d).isSome := by
  decide +kernel

theorem complement_eq_none_of_rootSelected :
    ∀ w ∈ words, w.choice = .rootSelected → complement w.terminals w.target = none := by
  decide +kernel

/-- In a word well formed under the resolution, a segment of the adjectival extended projection
or a functor taking adjectives attaches to a categorized core, never to a bare root, so its
realization is never selected by a root: adjectives take only the regular *-er* and *-est*, and
only the default nominalizers. -/
theorem complement_ne_none_of_wellFormed {ts : List Terminal} (hw : WellFormed Licenses ts)
    {i : ℕ} (hi : i < ts.length)
    (ht : ts[i] = .segment .adjectival ∨ ∃ p, ts[i] = .functor p [.adjectival]) :
    complement ts i ≠ none := by
  intro h
  have := hw i hi
  rw [h] at this
  rcases ht with ht | ⟨p, ht⟩ <;> simp [ht, Terminal.Takes] at this

theorem not_wellFormed_iff :
    ∀ w ∈ words, ¬ WellFormed Licenses w.terminals ↔
      ∃ p ∈ [CatFamily.verbal, .nominal], w.terminals.head? = some (.functor p [.adjectival]) := by
  decide +kernel

/-- **The puzzle of the adjective.** No licensing condition on the category of a complement both
derives the judgments of the paradigm and lets the verbalizers of the problem cases take what
their selection requires. *Too dance* shows that a bare root is not adjectival, while the
root-selected *-ify* of *clarify* takes an adjectival complement that, selection being local,
must be its root. -/
theorem not_exists_licensing :
    ¬ ∃ L : CatFamily → Option CatFamily → Prop,
      (∀ d ∈ data, d.judgment = .acceptable ↔ ∃ κ ∈ d.cores, L d.frame κ) ∧
      ∀ w ∈ words, w.choice = .rootSelected →
        ∀ t ∈ w.terminals[w.target]?, t.Takes L (complement w.terminals w.target) := by
  rintro ⟨L, hdata, hwords⟩
  have hdance : (⟨.adjectival, [none], .ungrammatical⟩ : Row) ∈ data := by decide +kernel
  have hclarify : (⟨[.functor .verbal [.adjectival]], 0, .rootSelected⟩ : Word) ∈ words := by
    decide +kernel
  obtain ⟨c, hc, hL⟩ := hwords _ hclarify rfl _ rfl
  obtain rfl : c = .adjectival := by simpa using hc
  exact absurd ((hdata _ hdance).mpr ⟨none, List.mem_singleton_self _, hL⟩) (by decide)

/-- In Distributed Morphology every stem is categorized by a head, so without ∅-Transparency no
inflection sees the root, and the past of *run* is no closer to its root than the past of
*instantiate*. With Embick's ∅-Transparency every root-selected inflection does see it. -/
theorem dm_seesRoot :
    ∀ w ∈ dmWords, ¬ w.spine.SeesRoot Embick2010.cyclic (fun _ ↦ False) w.target ∧
      (w.choice = .rootSelected →
        w.spine.SeesRoot Embick2010.cyclic Embick2010.phonNull w.target) := by
  decide +kernel

end Borer2013
