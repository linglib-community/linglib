module

public import Linglib.Core.Computability.ContextFreeGrammar.Dirichlet
public import Linglib.Core.Probability.Distributions.PitmanYor
public import Linglib.Core.Probability.UniformOn
public import Linglib.Data.Experiments.ODonnell2015
public import Linglib.Morphology.Exponence.Domain
public import Linglib.Morphology.Exponence.Select

/-!
# O'Donnell (2015): Productivity and Reuse in Language

In Chapter 7 of [odonnell-2015], the Dirichlet-multinomial PCFG (DMPCFG) and the maximum a
posteriori adaptor grammar (MAG) rank the unproductive *-ion* above the productive *-ness*, which
the book attributes to their estimating rules from token and type frequency (p. 268). This file
derives both rankings from the book's counts (`spectrum`, pp. 267–268), and Baayen's hapax-based
`P`, which ranks the two suffixes the other way.

## Main definitions

* `suffixGrammar ι`: nominalizations in *-ness* and *-ion* over a lexicon of stems `ι`.
* `AdaptorGrammar.prob`, `FragmentGrammar.prob`: the probability of an analysis from its counts.
* `FullListing.counts`, `FullListing.seating`: the MAG's analysis of a corpus.
* `Realizes D`: the corpus `D` has the book's counts.

## Implementation notes

The book measures a suffix's productivity by its probability on a novel stem of fixed probability
(p. 261, footnote 4), so two nominalizers are compared by their rule weights at `N`.

## TODO

* The FG's MAP grammar (§3.2), Figure 7.3 and Table 7.1; the data-oriented parsing estimators.

## References

* [odonnell-2015]
* [kiparsky-1973]
* [pitman-2006]
-/

@[expose] public section

namespace ODonnell2015

open ProbabilityTheory

/-! ## The suffix grammar -/

/-- The terminals of the suffix grammar over a lexicon of stems `ι`: adjective, verb and bound
stems, and the suffixes *-ness*, *-ion* and *-ate*. -/
inductive Sym (ι : Type) where
  | adj (i : ι)
  | v (i : ι)
  | bnd (i : ι)
  | ness
  | ion
  | ate
  deriving DecidableEq, Repr

/-- The nonterminals of the suffix grammar are nouns, adjectives, verbs, and the bound stems
that *-ate* attaches to (*segregat-*). -/
inductive SuffixNT where
  | N
  | Adj
  | V
  | BND
  deriving DecidableEq, Repr

section Grammar

variable {ι : Type}

/-- `N → Adj -ness`, the book's rule for *-ness*:Adj>N (p. 255). -/
def rNess : ContextFreeRule (Sym ι) SuffixNT :=
  ⟨.N, [.nonterminal .Adj, .terminal .ness]⟩

/-- `N → V -ion`, the rule for *-ion*:V>N. -/
def rIon : ContextFreeRule (Sym ι) SuffixNT :=
  ⟨.N, [.nonterminal .V, .terminal .ion]⟩

/-- `V → BND -ate`, the rule for *-ate*:BND>V, which attaches only to bound stems (p. 263). -/
def rAte : ContextFreeRule (Sym ι) SuffixNT :=
  ⟨.V, [.nonterminal .BND, .terminal .ate]⟩

/-- `Adj → adj i`, a stem of the lexicon, as `Adj → tall` in the book's grammar (Figure 7.1). -/
def rAdj (i : ι) : ContextFreeRule (Sym ι) SuffixNT :=
  ⟨.Adj, [.terminal (.adj i)]⟩

/-- `V → v i`. -/
def rV (i : ι) : ContextFreeRule (Sym ι) SuffixNT :=
  ⟨.V, [.terminal (.v i)]⟩

/-- `BND → bnd i`. -/
def rBnd (i : ι) : ContextFreeRule (Sym ι) SuffixNT :=
  ⟨.BND, [.terminal (.bnd i)]⟩

/-- The rule of the suffix grammar attaching a nominalizer. -/
def Suffix.rule : Suffix → ContextFreeRule (Sym ι) SuffixNT
  | .ness => rNess
  | .ion => rIon

theorem Suffix.rule_injective : Function.Injective (Suffix.rule (ι := ι)) := by
  intro s s' h
  cases s <;> cases s' <;> simp_all [Suffix.rule, rNess, rIon]

variable (ι) [Fintype ι] [DecidableEq ι]

/-- The suffix grammar over a lexicon of stems `ι`: nouns in *-ness* from adjectives and in
*-ion* from verbs, verbs in *-ate* from bound stems, and a stem of each category for each element
of `ι`. Unlike the book's grammar (Figure 7.1) it has no start symbol above `N`. -/
def suffixGrammar : ContextFreeGrammar (Sym ι) where
  NT := SuffixNT
  initial := .N
  rules := {rNess, rIon, rAte} ∪ Finset.univ.image rAdj ∪ Finset.univ.image rV ∪
    Finset.univ.image rBnd

/-- `DecidableEq` for the grammar's `NT` projection, which `ContextFreeGrammar.RulesWithLHS`
needs. Not synthesised automatically because `(suffixGrammar ι).NT` is a structure projection that
the typeclass solver does not reduce to `SuffixNT`. -/
instance : DecidableEq (suffixGrammar ι).NT :=
  inferInstanceAs (DecidableEq SuffixNT)

variable {ι}

theorem mem_rules {r : ContextFreeRule (Sym ι) (suffixGrammar ι).NT} :
    r ∈ (suffixGrammar ι).rules ↔ r = rNess ∨ r = rIon ∨ r = rAte ∨ (∃ i, r = rAdj i) ∨
      (∃ i, r = rV i) ∨ ∃ i, r = rBnd i := by
  simp only [suffixGrammar, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and, eq_comm (b := r)]
  tauto

theorem nonterminal_N_not_mem_output :
    ∀ r ∈ (suffixGrammar ι).rules, Symbol.nonterminal SuffixNT.N ∉ r.output := by
  intro r hr
  rcases mem_rules.mp hr with rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [rNess, rIon, rAte, rAdj, rV, rBnd]

theorem Suffix.rule_mem (s : Suffix) :
    s.rule ∈ (suffixGrammar ι).rules.filter (·.input = SuffixNT.N) := by
  cases s
  · exact Finset.mem_filter.mpr ⟨mem_rules.mpr (.inl rfl), rfl⟩
  · exact Finset.mem_filter.mpr ⟨mem_rules.mpr (.inr (.inl rfl)), rfl⟩

/-- The word a nominalizer forms on stem `i`, by `N → Adj -ness` over `Adj → adj i` or by
`N → V -ion` over `V → v i`. -/
def Suffix.word : Suffix → ι → RoseTree (Symbol (Sym ι) (suffixGrammar ι).NT)
  | .ness, i => .node (.nonterminal SuffixNT.N)
      [.node (.nonterminal SuffixNT.Adj) [.leaf (.terminal (.adj i))], .leaf (.terminal .ness)]
  | .ion, i => .node (.nonterminal SuffixNT.N)
      [.node (.nonterminal SuffixNT.V) [.leaf (.terminal (.v i))], .leaf (.terminal .ion)]

theorem Suffix.word_injective : Function.Injective fun p : Suffix × ι ↦ p.1.word p.2 := by
  rintro ⟨s, i⟩ ⟨s', i'⟩ h
  cases s <;> cases s' <;> simp_all [Suffix.word]

theorem Suffix.licensed_word (s : Suffix) (i : ι) :
    (s.word i).Licensed (suffixGrammar ι).Licenses := by
  cases s <;> simp [Suffix.word, RoseTree.licensed_node_iff, ContextFreeGrammar.Licenses, mem_rules,
    rNess, rIon, rAte, rAdj, rV, rBnd]

theorem Suffix.ruleAt?_word (s : Suffix) (i : ι) :
    RoseTree.ruleAt? (s.word i) [] = some s.rule := by
  cases s <;> rfl

theorem Suffix.ruleCount_word (s s' : Suffix) (i : ι) :
    RoseTree.ruleCount (N := (suffixGrammar ι).NT) s'.rule (s.word i) =
      if s = s' then 1 else 0 := by
  cases s <;> cases s' <;>
    simp [RoseTree.ruleCount, Suffix.word, Suffix.rule, rNess, rIon]

end Grammar

/-! ## The DMPCFG (§3.1.3, §3.1.4) -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- A corpus of derivations of the suffix grammar. -/
abbrev Corpus : Type :=
  Multiset (RoseTree (Symbol (Sym ι) (suffixGrammar ι).NT))

/-- The book's DMPCFG over the suffix grammar, with pseudo-count `1` for every rule (§3.5.5). -/
def dmpcfg : DirichletPCFG (suffixGrammar ι) :=
  ⟨fun _ ↦ 1, fun _ _ ↦ one_pos⟩

theorem dmpcfg_derivProb_word (x : ContextFreeRule (Sym ι) (suffixGrammar ι).NT → ℕ) (s : Suffix)
    (i : ι) : (dmpcfg.update x).mean.derivProb (s.word i) =
      .ofReal ((dmpcfg.update x).countsProb (RoseTree.ruleCounts {s.word i})) :=
  (dmpcfg.update x).derivProb_mean (s.licensed_word i)
    fun a ↦ by cases s <;> cases a <;> simp [Suffix.word]

/-! ## Adaptor and fragment grammars (§3.1.7, §3.1.8)

An adaptor grammar adds to a Dirichlet PCFG a Pitman–Yor restaurant at each nonterminal, whose
tables store derivations computed there. The book gives the probability of an analysis of a
corpus through its counts: `X`, the uses of each rule in building the trees stored at the tables,
one use per table, and `Y`, at each nonterminal the sizes of its tables, the numbers of uses of
the nonterminal that sat at each. A fragment grammar stores partial derivations: at each
nonterminal on the right-hand side of a rule it decides, by a beta-binomial urn, whether a stored
fragment continues there, and these decisions are its third kind of count, `Z`. The book's
hyperparameters are `π = 1`, `a = 0.5`, `b = 100` and `ψ = 50` (§3.5.5). -/

/-- The book's adaptor grammar over `G` adds to a Dirichlet PCFG a Pitman–Yor process memoizing
the derivations rooted at each nonterminal. -/
@[ext]
structure AdaptorGrammar {T : Type} (G : ContextFreeGrammar T) extends DirichletPCFG G where
  /-- The discount of the Pitman–Yor process at each nonterminal. -/
  discount : G.NT → ℝ
  /-- The concentration of the Pitman–Yor process at each nonterminal. -/
  concentration : G.NT → ℝ
  /-- The discount is nonnegative. -/
  discount_nonneg : ∀ a, 0 ≤ discount a
  /-- The discount is at most `1`. -/
  discount_le_one : ∀ a, discount a ≤ 1
  /-- The concentration exceeds minus the discount. With the bounds on the discount, this is the
  constraint under which the seating plan is a probability ([pitman-2006] (3.5)). -/
  neg_discount_lt_concentration : ∀ a, -discount a < concentration a

namespace AdaptorGrammar

variable {T : Type} {G : ContextFreeGrammar T} (M : AdaptorGrammar G)

/-- The Pitman–Yor probability of a seating at `a` whose tables have sizes `y`, the book's
Equation 3.14, the exchangeable partition probability function of [pitman-2006]. -/
noncomputable def pypFactor (a : G.NT) (y : Multiset ℕ) : ℝ :=
  pitmanYorEPPF (M.discount a) (M.concentration a) y

-- Theorem 3.2 [pitman-2006]
theorem pitmanYor_real_singleton_eq_pypFactor (a : G.NT) {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (pitmanYor (M.discount a) (M.concentration a) n).real {P} = M.pypFactor a P.partSizes :=
  pitmanYor_real_singleton (M.discount_nonneg a) (M.discount_le_one a)
    (M.neg_discount_lt_concentration a) P

theorem pypFactor_nonneg (a : G.NT) (y : Multiset ℕ) : 0 ≤ M.pypFactor a y :=
  pitmanYorEPPF_nonneg (M.discount_nonneg a) (M.discount_le_one a)
    (M.neg_discount_lt_concentration a) y

@[simp]
theorem pypFactor_zero (a : G.NT) : M.pypFactor a 0 = 1 := by
  simp [pypFactor, pitmanYorEPPF]

variable [DecidableEq G.NT]

/-- The probability of an analysis with rule counts `X` and table sizes `Y` (§3.1.7): the
Dirichlet-multinomial probability of the rule uses that built the stored trees, times the
Pitman–Yor probability of the seating at each nonterminal. The counts and the seating agree when
each nonterminal has as many tables as rule uses, as in the full-listing analysis
(`FullListing.card_seating`). -/
noncomputable def prob (X : ContextFreeRule T G.NT → ℕ) (Y : G.NT → Multiset ℕ) : ℝ :=
  M.countsProb X * ∏ a ∈ G.rules.image (·.input), M.pypFactor a (Y a)

theorem prob_nonneg (X : ContextFreeRule T G.NT → ℕ) (Y : G.NT → Multiset ℕ) : 0 ≤ M.prob X Y :=
  mul_nonneg (M.countsProb_pos X).le (Finset.prod_nonneg fun a _ ↦ M.pypFactor_nonneg a _)

@[simp]
theorem prob_zero : M.prob 0 0 = 1 := by
  simp [prob]

/-- With discount `1`, an analysis whose tables are all singletons has its DMPCFG probability, so
full parsing never reuses (p. 89). -/
theorem prob_replicate_one (h : ∀ a, M.discount a = 1) (X : ContextFreeRule T G.NT → ℕ)
    (n : G.NT → ℕ) : M.prob X (fun a ↦ Multiset.replicate (n a) 1) = M.countsProb X := by
  refine (congrArg _ (Finset.prod_eq_one fun a _ ↦ ?_)).trans (mul_one _)
  rw [pypFactor, h a]
  exact pitmanYorEPPF_one_replicate_one (by simpa [h a] using M.neg_discount_lt_concentration a) _

end AdaptorGrammar

/-- At a nonterminal slot of a rule, `recurse` continues the stored fragment and `halt` leaves the
slot open. -/
inductive FragmentGrammar.Decision
  | recurse
  | halt
  deriving DecidableEq, Fintype, Inhabited

/-- The book's fragment grammar over `G` adds to an adaptor grammar a Pólya urn over the
decisions at each nonterminal slot of each rule, with the beta parameters `ψ` as pseudo-counts. -/
@[ext]
structure FragmentGrammar {T : Type} (G : ContextFreeGrammar T) extends AdaptorGrammar G where
  /-- The pseudo-counts of the urn over the decisions at nonterminal slot `i` of rule `r`. -/
  slot : (r : ContextFreeRule T G.NT) → r.NonterminalPos → FragmentGrammar.Decision → ℝ
  /-- The pseudo-counts are positive. -/
  slot_pos : ∀ r i d, 0 < slot r i d

namespace FragmentGrammar

variable {T : Type} {G : ContextFreeGrammar T} [DecidableEq G.NT]

/-- The decision counts `Z` record how often each decision was taken at each nonterminal slot of
each rule. -/
abbrev SlotCounts (G : ContextFreeGrammar T) : Type :=
  (r : ContextFreeRule T G.NT) → r.NonterminalPos → Decision → ℕ

variable (M : FragmentGrammar G)

/-- The probability of an analysis with counts `X`, `Y` and `Z` (§3.1.8): the adaptor-grammar
probability of `X` and `Y`, times, at each nonterminal slot of each rule, the urn probability of
the decisions taken there. The decisions at the slots of a rule agree with `X` when they number
the rule's uses in `X`, which is the caller's hypothesis. -/
noncomputable def prob (X : ContextFreeRule T G.NT → ℕ) (Y : G.NT → Multiset ℕ)
    (Z : SlotCounts G) : ℝ :=
  M.toAdaptorGrammar.prob X Y * ∏ r ∈ G.rules, ∏ i, polyaUrnProb (M.slot r i) (Z r i)

theorem prob_nonneg (X : ContextFreeRule T G.NT → ℕ) (Y : G.NT → Multiset ℕ) (Z : SlotCounts G) :
    0 ≤ M.prob X Y Z :=
  mul_nonneg (M.toAdaptorGrammar.prob_nonneg X Y) <| Finset.prod_nonneg fun r _ ↦
    Finset.prod_nonneg fun i _ ↦ (polyaUrnProb_pos (M.slot_pos r i) _).le

@[simp]
theorem prob_zero : M.prob 0 0 0 = 1 := by
  simp only [prob, AdaptorGrammar.prob_zero, one_mul]
  exact Finset.prod_eq_one fun r _ ↦ Finset.prod_eq_one fun i _ ↦ polyaUrnProb_zero (M.slot r i)

end FragmentGrammar

/-! ### The full-listing analysis

The MAG stores each computation in its entirety the first time it is computed (§2.4.2), and its
maximum a posteriori analysis of a corpus of derivations stores each distinct derivation once
(§3.3, and p. 77, footnote 24): its tables at a nonterminal are the distinct subtrees of the
corpus rooted there. A word of the corpus sits at the table of its derivation, and the children of
a stored derivation, computed when it was stored, sit at the tables of their own derivations. -/

namespace FullListing

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]
  (D : Multiset (RoseTree (Symbol T G.NT)))

/-- The distinct subtrees of the words of the corpus. -/
def subtrees : Finset (RoseTree (Symbol T G.NT)) :=
  D.toFinset.biUnion fun t ↦ t.subtrees.toFinset

/-- The rule counts `X` of the full-listing analysis count the stored derivations with each rule
at the root, since each table used its root rule once. -/
def counts (r : ContextFreeRule T G.NT) : ℕ :=
  ((subtrees D).filter (RoseTree.ruleAt? (g := G) · [] = some r)).card

/-- The customers at the table of a stored derivation `s` are the words of the corpus that are
`s` and the occurrences of `s` among the children of the stored derivations. -/
def customers (s : RoseTree (Symbol T G.NT)) : ℕ :=
  D.count s + ∑ u ∈ subtrees D, u.children.count s

/-- The table sizes `Y` of the full-listing analysis at `a` are the numbers of customers at the
tables of the stored derivations rooted at `a`. -/
def seating (a : G.NT) : Multiset ℕ :=
  ((subtrees D).filter (·.value = .nonterminal a)).val.map (customers D)

theorem card_seating (hD : ∀ t ∈ D, t.Licensed G.Licenses) (a : G.NT) :
    Multiset.card (seating D a) = ∑ r ∈ G.rules.filter (·.input = a), counts D r := by
  rw [seating, Multiset.card_map, ← Finset.card_def,
    Finset.card_eq_sum_card_fiberwise (t := G.rules.filter (·.input = a))
      (f := fun s ↦ (⟨a, s.children.map RoseTree.value⟩ : ContextFreeRule T G.NT)) fun s hs ↦ ?_]
  · refine Finset.sum_congr rfl fun r hr ↦ congrArg Finset.card (Finset.ext fun s ↦ ?_)
    obtain ⟨A, w⟩ := r
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hr
    simp [Finset.mem_filter, RoseTree.ruleAt?_nil_eq_some_iff, and_assoc]
  · obtain ⟨hsub, hv⟩ := Finset.mem_filter.mp hs
    obtain ⟨t, ht, hst⟩ : ∃ t ∈ D, RoseTree.IsSubtree s t := by
      simpa [subtrees, RoseTree.mem_subtrees] using hsub
    have hlic := hD t ht s hst
    rw [hv] at hlic
    exact Finset.mem_filter.mpr ⟨hlic, rfl⟩

/-- **At a nonterminal on no right-hand side the full-listing counts are type counts.** If no rule
has `r`'s left-hand side among its children, the derivations stored with `r` at the root are the
word types of the corpus formed with `r`. -/
theorem counts_eq_card_filter_toFinset (hD : ∀ t ∈ D, t.Licensed G.Licenses)
    {r : ContextFreeRule T G.NT} (hr : ∀ r' ∈ G.rules, .nonterminal r.input ∉ r'.output) :
    counts D r = (D.toFinset.filter (RoseTree.ruleAt? (g := G) · [] = some r)).card := by
  refine congrArg Finset.card (Finset.ext fun s ↦ ?_)
  simp only [subtrees, Finset.mem_filter, Finset.mem_biUnion, Multiset.mem_toFinset,
    List.mem_toFinset, RoseTree.mem_subtrees]
  refine ⟨fun ⟨⟨t, ht, hst⟩, hs⟩ ↦ ⟨?_, hs⟩, fun ⟨hs, hrs⟩ ↦ ⟨⟨s, hs, .refl s⟩, hrs⟩⟩
  by_contra hsD
  obtain ⟨r', hr', hmem⟩ :=
    (hD t ht).exists_mem_output_of_isSubtree hst fun h ↦ hsD (h ▸ ht)
  exact hr r' hr' ((RoseTree.ruleAt?_nil_eq_some_iff.mp hs).1 ▸ hmem)

end FullListing

/-! ## Token frequency, type frequency and hapaxes (§7.3.1) -/

section Counts

/-- The tokens of a nominalizer in a corpus are the uses of its rule. -/
def tokens (D : Corpus ι) (s : Suffix) : ℕ :=
  RoseTree.ruleCounts (N := (suffixGrammar ι).NT) D s.rule

/-- The word types of a nominalizer in a corpus are the distinct words formed with its rule. -/
def wordTypes (D : Corpus ι) (s : Suffix) :
    Finset (RoseTree (Symbol (Sym ι) (suffixGrammar ι).NT)) :=
  D.toFinset.filter (RoseTree.ruleAt? · [] = some s.rule)

/-- The hapax legomena of a nominalizer in a corpus are its word types that occur once. -/
def hapaxes (D : Corpus ι) (s : Suffix) : ℕ :=
  ((wordTypes D s).filter (D.count · = 1)).card

/-- Baayen's category-conditioned degree of productivity `P` of a nominalizer is the ratio of its
hapaxes to its tokens (Equation 6.9). -/
noncomputable def baayenP (D : Corpus ι) (s : Suffix) : ℝ :=
  hapaxes D s / tokens D s

/-- A corpus realizes the book's counts when each nominalizer has the tokens, word types and
hapaxes of pp. 267–268. -/
structure Realizes (D : Corpus ι) : Prop where
  tokens_eq : ∀ s, tokens D s = (spectrum s).wordTokens
  card_wordTypes_eq : ∀ s, (wordTypes D s).card = (spectrum s).wordTypes
  hapaxes_eq : ∀ s, hapaxes D s = (spectrum s).hapaxes

namespace Realizes

variable {D : Corpus ι}

/-- With unit pseudo-counts, the DMPCFG ranks *-ion* above *-ness* on a corpus with the book's
counts (§3.5.5, §3.3, p. 74). -/
theorem dmpcfg_ness_lt_ion (h : Realizes D) :
    (PCFG.relFreq D).weight Suffix.ness.rule < (PCFG.relFreq D).weight Suffix.ion.rule := by
  refine (PCFG.ofCounts_weight_lt_ofCounts_weight_iff (r := ⟨_, Suffix.ness.rule_mem⟩)
    (r' := ⟨_, Suffix.ion.rule_mem⟩)).mpr ?_
  change tokens D .ness < tokens D .ion
  rw [h.tokens_eq, h.tokens_eq]
  decide

/-- With unit pseudo-counts, the MAG ranks *-ion* above *-ness* on a corpus of licensed derivations
with the book's counts (§3.3, p. 75). -/
theorem mag_ness_lt_ion (hD : ∀ t ∈ D, t.Licensed (suffixGrammar ι).Licenses)
    (h : Realizes D) :
    (PCFG.ofCounts (FullListing.counts D)).weight Suffix.ness.rule <
      (PCFG.ofCounts (FullListing.counts D)).weight Suffix.ion.rule := by
  refine (PCFG.ofCounts_weight_lt_ofCounts_weight_iff (r := ⟨_, Suffix.ness.rule_mem⟩)
    (r' := ⟨_, Suffix.ion.rule_mem⟩)).mpr ?_
  rw [FullListing.counts_eq_card_filter_toFinset D hD nonterminal_N_not_mem_output,
    FullListing.counts_eq_card_filter_toFinset D hD nonterminal_N_not_mem_output]
  change (wordTypes D .ness).card < (wordTypes D .ion).card
  rw [h.card_wordTypes_eq, h.card_wordTypes_eq]
  decide

/-- **Baayen's `P` ranks *-ness* above *-ion*.** -/
theorem baayenP_ion_lt_ness (h : Realizes D) : baayenP D .ion < baayenP D .ness := by
  simp only [baayenP, h.hapaxes_eq, h.tokens_eq]
  norm_num [spectrum]

end Realizes

end Counts

/-! ### A corpus with the book's counts -/

section Witness

/-- The corpus in which the word of `s` on stem `i` occurs `m s i` times. -/
def corpus (m : Suffix → ι → ℕ) : Corpus ι :=
  ∑ s, ∑ i, m s i • {s.word i}

theorem mem_corpus {m : Suffix → ι → ℕ} {t : RoseTree (Symbol (Sym ι) (suffixGrammar ι).NT)} :
    t ∈ corpus m ↔ ∃ s i, m s i ≠ 0 ∧ s.word i = t := by
  simp [corpus, Multiset.mem_sum, Multiset.mem_nsmul, eq_comm]

theorem licensed_of_mem_corpus {m : Suffix → ι → ℕ}
    {t : RoseTree (Symbol (Sym ι) (suffixGrammar ι).NT)} (ht : t ∈ corpus m) :
    t.Licensed (suffixGrammar ι).Licenses := by
  obtain ⟨s, i, -, rfl⟩ := mem_corpus.mp ht
  exact s.licensed_word i

theorem count_corpus (m : Suffix → ι → ℕ) (s : Suffix) (i : ι) :
    (corpus m).count (s.word i) = m s i := by
  have key (s' : Suffix) (i' : ι) : (m s' i' • {s'.word i'} : Corpus ι).count (s.word i) =
      if (s', i') = (s, i) then m s' i' else 0 := by
    rw [Multiset.count_nsmul, Multiset.count_singleton]
    by_cases h : (s', i') = (s, i)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp
    · rw [ite_eq_right (fun h' ↦ h (Suffix.word_injective
        (show (fun p : Suffix × ι ↦ p.1.word p.2) (s', i') = _ from h'.symm))), ite_eq_right h,
        mul_zero]
  simp only [corpus, Multiset.count_sum', key]
  rw [← Fintype.sum_prod_type' fun s' i' ↦ if (s', i') = (s, i) then m s' i' else 0]
  simp

theorem tokens_corpus (m : Suffix → ι → ℕ) (s : Suffix) : tokens (corpus m) s = ∑ i, m s i := by
  simp [tokens, corpus, map_sum, map_nsmul, Finset.sum_apply, Suffix.ruleCount_word]

theorem wordTypes_corpus (m : Suffix → ι → ℕ) (s : Suffix) :
    wordTypes (corpus m) s = (Finset.univ.filter (m s · ≠ 0)).image s.word := by
  ext t
  simp only [wordTypes, Finset.mem_filter, Multiset.mem_toFinset, mem_corpus, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨s', i, hm, rfl⟩, hr⟩
    obtain rfl := Suffix.rule_injective (Option.some.inj ((s'.ruleAt?_word i).symm.trans hr))
    exact ⟨i, hm, rfl⟩
  · rintro ⟨i, hm, rfl⟩
    exact ⟨⟨s, i, hm, rfl⟩, s.ruleAt?_word i⟩

theorem card_wordTypes_corpus (m : Suffix → ι → ℕ) (s : Suffix) :
    (wordTypes (corpus m) s).card = (Finset.univ.filter (m s · ≠ 0)).card := by
  rw [wordTypes_corpus, Finset.card_image_of_injective _
    fun i i' h ↦ (Prod.mk.inj (Suffix.word_injective (a₁ := (s, i)) (a₂ := (s, i')) h)).2]

theorem hapaxes_corpus (m : Suffix → ι → ℕ) (s : Suffix) :
    hapaxes (corpus m) s = (Finset.univ.filter (m s · = 1)).card := by
  rw [hapaxes, wordTypes_corpus, Finset.filter_image, Finset.card_image_of_injective _
    fun i i' h ↦ (Prod.mk.inj (Suffix.word_injective (a₁ := (s, i)) (a₂ := (s, i')) h)).2]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, count_corpus]
  omega

/-- Multiplicities realizing the book's counts over `1117` stems: the first `hapaxes` stems once,
the others up to the last word type twice, and the remaining tokens on the last word type. -/
def bookMult (s : Suffix) (i : Fin 1117) : ℕ :=
  if (i : ℕ) < (spectrum s).hapaxes then 1
  else if (i : ℕ) + 1 < (spectrum s).wordTypes then 2
  else if (i : ℕ) + 1 = (spectrum s).wordTypes then
    (spectrum s).wordTokens - (spectrum s).hapaxes -
      2 * ((spectrum s).wordTypes - 1 - (spectrum s).hapaxes)
  else 0

/-- **The book's counts are realized** by a corpus of licensed derivations of the suffix grammar,
so the theorems on `Realizes` apply. -/
theorem exists_realizes : ∃ D : Corpus (Fin 1117),
    (∀ t ∈ D, t.Licensed (suffixGrammar (Fin 1117)).Licenses) ∧ Realizes D :=
  ⟨corpus bookMult, fun _ ↦ licensed_of_mem_corpus,
    ⟨fun s ↦ by rw [tokens_corpus]; cases s <;> decide +kernel,
      fun s ↦ by rw [card_wordTypes_corpus]; cases s <;> decide +kernel,
      fun s ↦ by rw [hapaxes_corpus]; cases s <;> decide +kernel⟩⟩

end Witness

/-! ## The probabilistic Elsewhere Condition (§5.5.3)

[odonnell-2015] §5.5.3 derives the Elsewhere Condition from probabilistic inference alone. Rules
define distributions over the forms they generate, so a rule whose support properly includes
another's must assign lower probability to each of those forms, on average, and conditioning on a
form preserves the preference. The book quotes [kiparsky-1973]'s formulation, preferring `r₂` when
`Inputs(r₂) ⊂ Inputs(r₁)`, which is `Morphology.Exponence.Rule`'s specificity order.

A rule's support is the domain of an `Exponence.DomainRule`, and when each rule generates its
domain uniformly the preference holds at every shared form, not only on average: a properly
narrower domain gives each of its forms more probability
(`MeasureTheory.uniformOn_finset_real_singleton_lt_of_ssubset`). A rule maximizing the
probability of a form among the rules generating it is then an Elsewhere winner, since higher
probability is a smaller domain and a smaller domain contained in another is equal to it. -/

section ProbabilisticElsewhere

open Morphology Morphology.Exponence MeasureTheory

variable {Ctx F : Type*} [DecidableEq Ctx]

theorem selectByCard_isElsewhereWinner {v : RuleSet (DomainRule Ctx F)} {c : Ctx}
    {r : DomainRule Ctx F} (h : v.selectBy (fun s ↦ OrderDual.toDual s.dom.card) c = some r) :
    v.IsElsewhereWinner (·.dom) c r :=
  RuleSet.selectBy_isElsewhereWinner (f := fun s : DomainRule Ctx F ↦ OrderDual.toDual s.dom.card)
    (fun _ _ _ _ h ↦ OrderDual.toDual_lt_toDual.2 (Finset.card_lt_card h)) h

variable [MeasurableSpace Ctx] [MeasurableSingletonClass Ctx]

/-- **Elsewhere selection is maximum-likelihood inference.** A rule that gives a form at least the
probability any other rule generating it does, each rule generating its domain uniformly, is an
Elsewhere winner at that form (§5.5.3). -/
theorem isElsewhereWinner_of_forall_uniformOn_le {v : RuleSet (DomainRule Ctx F)} {c : Ctx}
    {r : DomainRule Ctx F} (hrv : r ∈ v) (hrc : c ∈ r.dom)
    (hmax : ∀ s ∈ v, c ∈ s.dom →
      (uniformOn (s.dom : Set Ctx)).real {c} ≤ (uniformOn (r.dom : Set Ctx)).real {c}) :
    v.IsElsewhereWinner (·.dom) c r := by
  refine ⟨⟨hrv, hrc⟩, fun s ⟨hsv, hsc⟩ (hle : s.dom ⊆ r.dom) ↦ ?_⟩
  have hsc : c ∈ s.dom := hsc
  exact (Finset.eq_of_subset_of_card_le hle
    ((uniformOn_finset_real_singleton_le_iff hsc hrc).mp (hmax s hsv hsc))).symm.subset

end ProbabilisticElsewhere

end ODonnell2015
