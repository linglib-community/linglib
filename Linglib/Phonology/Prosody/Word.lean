module

public import Linglib.Phonology.Prosody.Domination

/-!
# Prosodic words (ω)

A prosodic word ω is a node of the prosodic tree, and `IsWord` is its well-formedness on that
carrier: an ω-node dominating only feet, prosodic words and stray syllables, the Layeredness of
[selkirk-1996]. A stray syllable and an ω over an ω (the extended prosodic word of
[ito-mester-2009]) are admitted, since Exhaustivity and Nonrecursivity are violable; a
[nonrecursive word](##Prosody.isWord_children) has only feet and syllables as daughters. The
word-size notions `MinimalWord`, `MaximalWord` and `PerfectWord` are stated over the feet of the
tree, and [the perfect word is the one that is both minimal and
maximal](##Prosody.perfectWord_iff_minimal_and_maximal).

## Implementation notes

The Optimality-theoretic studies score candidate trees that `IsWord` rules out, so theorems take
`IsWord` as a hypothesis on the tree and there is no subtype of words. `IsWord` does not require
a foot: [dolatian-2020] reports languages with ω directly over σ, and candidates often leave
foot structure out.

## References

* [selkirk-1980]
* [nespor-vogel-1986]
* [liberman-prince-1977]
* [hayes-1995]
* [mccarthy-prince-1993]
* [prince-smolensky-1993]
* [selkirk-1996]
* [ito-mester-2003]
* [ito-mester-2009]
* [dolatian-2020]
* [uchihara-mendozaruiz-2021]
-/

@[expose] public section

namespace Prosody

/-! ### Prosodic OT constraints over the `Tree` carrier

The violable constraints scoring prosodic candidates are `OptimalityTheory.Constraint Tree`
values ([prince-smolensky-1993]); a grammar ranks them and scores with the OT engine
(`OptimalityTheory.Tableau.ofList`). They are defined on the **carrier** `Tree` (which
holds the ill-formed candidates `IsWord` rules out). List-recursion auxes
are local `where`s. -/

open OptimalityTheory

variable {M : Type*}

/-- **Parse-into-`ℓ`** ([ito-mester-2003]) counts σ-leaves dominated by no `ℓ`-node. -/
def parseInto (ℓ : Level) : Constraint (RoseTree (Constituent Level M)) := fun t => go false t where
  go (under : Bool) : RoseTree (Constituent Level M) → Nat
    | .node a cs =>
        let u := under || decide (a.level = ℓ)
        (if a.level = .syl ∧ cs = [] ∧ u = false then 1 else 0) + goList u cs
  goList (under : Bool) : List (RoseTree (Constituent Level M)) → Nat
    | [] => 0
    | c :: cs => go under c + goList under cs

/-- The σ-weight content of a foot node's direct σ-daughters. -/
def footContent (cs : List Tree) : List Syllable.Weight :=
  cs.filterMap fun c => match c with
    | .node a [] => a.weight?
    | _ => none

/-- The feet of a prosodic tree are the σ-weight contents of its `f`-nodes. -/
def feet : Tree → List (List Syllable.Weight) := fun t => go t where
  go : Tree → List (List Syllable.Weight)
    | .node a cs => (if a.level = .ft then [footContent cs] else []) ++ goList cs
  goList : List Tree → List (List Syllable.Weight)
    | [] => []
    | t :: ts => go t ++ goList ts

/-- Syllables parsed into no foot — `parseInto .ft`. -/
def unfootedCount (t : Tree) : Nat := parseInto .ft t

/-- The total mora count is the sum of the tree's σ-weights. -/
def moraCount : Tree → Nat := fun t => go t where
  go : Tree → Nat
    | .node a cs => a.weight?.getD 0 + goList cs
  goList : List Tree → Nat
    | [] => 0
    | t :: ts => go t + goList ts

/-! ### The well-formed prosodic word ω

`IsWord` is the Layeredness of [selkirk-1996] at the word: a tree rooted in an ω-node and
licensed by `Constituent.Licenses`. Licensing is decidable, so a winner can be certified
`IsWord` by `decide`. -/

/-- A well-formed prosodic word is a licensed tree rooted in an ω-node, so an ω-node dominating
    only feet, prosodic words and stray syllables, never φ or ι: the Layeredness of
    [selkirk-1996]. A foot daughter is not required, since [dolatian-2020] reports languages
    with ω directly over σ and candidates often leave foot structure out; a stray σ and an ω
    over an ω are admitted, Exhaustivity and Nonrecursivity being violable. -/
abbrev IsWord : RoseTree (Constituent Level M) → Prop := IsConstituent .om

/-- The daughters of a word without recursion are feet and stray syllables. -/
theorem isWord_children {a : Constituent Level M} {cs : List (RoseTree (Constituent Level M))}
    (hw : IsWord (.node a cs)) (hr : noRec (.node a cs) = 0) :
    a.level = .om ∧ ∀ c ∈ cs, IsFoot c ∨ (c.value.level = .syl ∧ c.children = []) := by
  have ha : a.level = .om := hw.1
  refine ⟨ha, fun c hc ↦ ?_⟩
  have hcl := (hw.of_mem_children (c := c) hc).2
  have hle : c.value.level ≤ .om := by
    rw [← ha]
    exact layeredness_eq_zero_iff.1 hw.layeredness_eq_zero _ (.refl _) c (.of_mem_children hc)
  have hne : c.value.level ≠ .om := by
    rw [← ha]
    exact nonrecursivity_eq_zero_iff.1 (noRec_eq_zero_iff.1 hr _) _ (.refl _) rfl c hc
  rcases c with ⟨cl, ccs⟩
  simp only [RoseTree.value_node, RoseTree.children_node] at hle hne ⊢
  cases hlv : cl.level with
  | syl =>
    have h := (RoseTree.licensed_node_iff.mp hcl).1
    rw [Constituent.Licenses, hlv] at h
    exact Or.inr ⟨rfl, by simpa [Level.Licenses] using h⟩
  | ft => exact Or.inl ⟨hlv, hcl⟩
  | om => exact absurd hlv hne
  | ph => rw [hlv] at hle; exact absurd hle (by decide)
  | iota => rw [hlv] at hle; exact absurd hle (by decide)

/-! ### Word-size predicates -/

variable {measure : List Syllable.Weight → ℕ} {t : Tree}

/-- A minimal word ([mccarthy-prince-1993]) contains a well-formed foot (PrWd ⊇ Ft). -/
def MinimalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  ∃ f ∈ feet t, measure f = 2
instance : Decidable (MinimalWord measure t) := by unfold MinimalWord; infer_instance

/-- A maximal word ([uchihara-mendozaruiz-2021]) has at most one well-formed foot and is
    exhaustively parsed, the upper size bound. -/
def MaximalWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length ≤ 1 ∧ unfootedCount t = 0 ∧ ∀ f ∈ feet t, measure f = 2
instance : Decidable (MaximalWord measure t) := by unfold MaximalWord; infer_instance

/-- The perfect prosodic word ([ito-mester-2009]) is an ω coextensive with one well-formed
    foot. -/
def PerfectWord (measure : List Syllable.Weight → ℕ) (t : Tree) : Prop :=
  (feet t).length = 1 ∧ (∀ f ∈ feet t, measure f = 2) ∧ unfootedCount t = 0
instance : Decidable (PerfectWord measure t) := by unfold PerfectWord; infer_instance

theorem PerfectWord.minimal (h : PerfectWord measure t) : MinimalWord measure t := by
  obtain ⟨hlen, hwf, _⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · rw [hfeet] at hlen; simp at hlen
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

/-- A perfect word is maximal. -/
theorem PerfectWord.maximal (h : PerfectWord measure t) : MaximalWord measure t := by
  obtain ⟨hlen, hwf, hu⟩ := h
  exact ⟨hlen.le, hu, hwf⟩

theorem perfectWord_iff_minimal_and_maximal :
    PerfectWord measure t ↔ MinimalWord measure t ∧ MaximalWord measure t := by
  refine ⟨fun h => ⟨h.minimal, h.maximal⟩, ?_⟩
  rintro ⟨⟨f, hf, _⟩, hle, hu, hwf⟩
  have h1 : 0 < (feet t).length := List.length_pos_of_mem hf
  exact ⟨le_antisymm hle (by omega), hwf, hu⟩

theorem MaximalWord.minimal (hne : feet t ≠ []) (h : MaximalWord measure t) :
    MinimalWord measure t := by
  obtain ⟨_, _, hwf⟩ := h
  rcases hfeet : feet t with _ | ⟨f, fs⟩
  · exact absurd hfeet hne
  · exact ⟨f, by rw [hfeet]; simp, hwf f (by rw [hfeet]; simp)⟩

/-! ### Worked examples -/

-- A bimoraic foot, the perfect word over it, and a recursive (ω-over-ω) word.
private def exFoot : Tree := .ft [.σ 2]
private def perfectW : Tree := .om [exFoot]
private def recursiveW : Tree := .om [.σ 1, .om [exFoot]]

-- Well-formedness: a flat ω over a foot and a recursive ω are both legal words — ω-over-ω
-- is admitted (No-Recursion is violable). A φ-node inside an ω violates Layeredness.
example : IsWord perfectW := by decide
example : IsWord recursiveW := by decide
example : ¬ IsWord (.om [.ph []] : Tree) := by decide

-- `noRec` reads the No-Recursion cost off the carrier: the recursive word scores
-- one ω-over-ω, the flat one zero.
example : noRec recursiveW = 1 := by decide
example : noRec perfectW = 0 := by decide

-- The ω-over-ω word has the outer ω as its sole maximal projection and the inner ω as its
-- sole minimal projection; the perfect (flat) word is both at once.
example : recursiveW.vertices.filter (⟨·⟩ ∈ maximalProjections .om recursiveW) = [[]] := by
  decide
example : recursiveW.vertices.filter (⟨·⟩ ∈ minimalProjections .om recursiveW) = [[1]] := by
  decide
example : perfectW.vertices.filter (⟨·⟩ ∈ maximalProjections .om perfectW) = [[]] := by
  decide
example : perfectW.vertices.filter (⟨·⟩ ∈ minimalProjections .om perfectW) = [[]] := by
  decide

end Prosody
