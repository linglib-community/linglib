module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Benua 1997: transderivational identity

Benua proposes that morphologically related words are held identical by
ranked, violable constraints on an output–output (OO) correspondence relation
between two surface words, each also tied to its own input by IO-faithfulness
(the subparadigm (11)). Misapplication — overapplication, `OO-Identity, M >>
IO-Faith` (21); underapplication, `OO-Identity >> M >> IO-Faith` (28); and its
restriction TETRU, `M₁ >> OO-Identity >> M₂ >> IO-Faith` (35) — falls out of
ranking, with no cyclic derivation. What lets a dominated constraint compel
violation of a dominant one is *recursive evaluation* (§2.3.1): the hierarchy
is duplicated, the base's recursion dominating the derived word's, so
misapplication in the base is always fatal (the priority of the base) and a
paradigm competes by the base's violation profile first and the derived word's
second. `recursive` states this over the substrate's `Correspondence`, `Constraint` and
`Tableau`; `nonrecursive` is the summed evaluation the paper shows going wrong
in (57), (88) and (119); when the candidates share their base, recursive
evaluation is evaluation of the derived word (`optimal_tableau_recursive`).

The paper's tableaux then run as stated: the English diminutive paradigm
*Larry ~ Lar* ((16), (29)); Sundanese nasal harmony from any rich input (47),
its overapplication in infixed plurals (52), its normal application under a
nasal affix (55) and the base that must not overapply (56) versus (57); Tiberian
Hebrew jussive truncation with epenthesis underapplying (87) versus (88), TETRU
forcing it in rising-sonority clusters (92) and the emergent markedness relation
`SON-CON ⊆ *COMPLEX-CODA`, spirantization underapplying in 2fs truncation (118)
versus (119), and the imperative's normal application (135) — the two truncations
under the single ranking (137), distinguished only by which OO relation their
morphology invokes (§4.6.3). Out of scope: English affix classes (Ch. 5), the
guttural CODACOND (§4.3.3), opacity (§4.4.3), and the serial alternatives (§3.5,
§4.7), which the paper rejects as over-generating rather than reconstructs.

## References

* [benua-1997]
* [cohn-1990]
-/

@[expose] public section

namespace Benua1997

open OptimalityTheory
open OptimalityTheory.Correspondence (diagonalPairs)

variable {α : Type*} {ρ : Type*}

/-! ### Subparadigms and recursive evaluation -/

/-- The four positions of a subparadigm (11), each word with its own input. -/
inductive Role
  | baseInput | base | derivInput | derivative
  deriving DecidableEq, Repr

/-- A subparadigm has the base and the derived word with their inputs, and the three
correspondence relations of (11), each word's IO relation and the OO relation. -/
def paradigm (bIn b dIn d : List α) (ioB ioD oo : List (ℕ × ℕ)) : Correspondence Role α :=
  .ofPairs (fun | .baseInput => bIn | .base => b | .derivInput => dIn | .derivative => d)
    fun | .baseInput, .base => ioB | .derivInput, .derivative => ioD | .base, .derivative => oo
        | _, _ => []

/-- A constraint of the hierarchy is read at each word of the subparadigm. A markedness
constraint reads the word's output, IO-Faith its IO relation, and OO-Identity the OO
relation, being vacuous at the base, which bears none (§2.3.1). -/
structure ParadigmConstraint (α : Type*) where
  atBase : Correspondence Role α → ℕ
  atDerived : Correspondence Role α → ℕ

/-- A markedness constraint, read off each output. -/
def markedness (m : List α → ℕ) : ρ → ParadigmConstraint α :=
  fun _ ↦ ⟨fun c ↦ m (c.form .base), fun c ↦ m (c.form .derivative)⟩

/-- An IO-Faith constraint, read off each word's IO relation. -/
def ioFaith (f : Correspondence Role α → Role → Role → ℕ) : ρ → ParadigmConstraint α :=
  fun _ ↦ ⟨fun c ↦ f c .baseInput .base, fun c ↦ f c .derivInput .derivative⟩

/-- The OO-Identity constraint proper to the relation `rel` is read off the OO relation of a
paradigm bearing `rel`, and is vacuous on paradigms bearing another (§4.6.3) and at the base. -/
def ooIdentity [DecidableEq ρ] (rel : ρ) (f : Correspondence Role α → Role → Role → ℕ) :
    ρ → ParadigmConstraint α :=
  fun r ↦ ⟨fun _ ↦ 0, fun c ↦ if r = rel then f c .base .derivative else 0⟩

/-- Recursive evaluation (§2.3.1) duplicates the ranking and ranks the recursions, the base's
above the derived word's, for paradigms bearing relation `r`. -/
def recursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence Role α)) :=
  ranking.map (fun k ↦ (k r).atBase) ++ ranking.map (fun k ↦ (k r).atDerived)

/-- Non-recursive evaluation, each constraint's violations tallied over both words — the
evaluation of (57), (88), (119). -/
def nonrecursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence Role α)) :=
  ranking.map fun k c ↦ (k r).atBase c + (k r).atDerived c

/-- The tableau of the labelled candidate paradigms `cand` under `eval` — `recursive` or
`nonrecursive` — for paradigms bearing `r`. -/
def tableau {L : Type*} [DecidableEq L] (cand : L → Correspondence Role α) (labels : Finset L)
    (eval : List (ρ → ParadigmConstraint α) → ρ → List (Constraint (Correspondence Role α)))
    (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :=
  Tableau.ofList labels ((eval ranking r).map (Constraint.comap cand))

/-- Candidates that share their base rate alike in the base's recursion, so recursive evaluation
of them is evaluation of the derived word. -/
theorem optimal_tableau_recursive {L : Type*} [DecidableEq L] {cand : L → Correspondence Role α}
    {labels : Finset L} {ranking : List (ρ → ParadigmConstraint α)} {r : ρ}
    (h : ∀ k ∈ ranking, ∀ x ∈ labels, ∀ y ∈ labels, (k r).atBase (cand x) = (k r).atBase (cand y)) :
    (tableau cand labels recursive ranking r).optimal =
      (Tableau.ofList labels (ranking.map fun k ↦ (k r).atDerived ∘ cand)).optimal := by
  rw [tableau, recursive, List.map_append, Tableau.optimal_ofList_append_of_forall_eq, List.map_map]
  · rfl
  · simp only [List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩ x hx y hy
    exact h k hk x hx y hy

/-- The candidate paradigms of a four-way tableau. -/
inductive Cand4
  | a | b | c | d
  deriving DecidableEq, Repr

/-- The candidate paradigms of a three-way tableau. -/
inductive Cand3
  | a | b | c
  deriving DecidableEq, Repr

/-! ### English diminutive truncation (§2.3.1)

*L[æ]rry ~ L[æ]r*: the a/æ neutralisation before tautosyllabic *r* underapplies in the
diminutive, under `OO-IDENT[BK] >> *ær]σ >> IO-IDENT[BK]` (15). -/

namespace English

/-- The segments of *Larry*. -/
inductive Seg
  | l | r | i | a | ae
  deriving DecidableEq, Repr

/-- Backness of the low vowels. -/
def back : Seg → Option Bool
  | .a => some true
  | .ae => some false
  | _ => none

/-- `*ær]σ` bans a front low vowel before a syllable-closing *r*. -/
def aerSigma : List Seg → ℕ
  | .ae :: .r :: rest => (if rest.head? = some .i then 0 else 1) + aerSigma (.r :: rest)
  | _ :: rest => aerSigma rest
  | [] => 0

/-- The ranking (15), `OO-IDENT[BK] >> *ær]σ >> IO-IDENT[BK]`. -/
def ranking : List (Unit → ParadigmConstraint Seg) :=
  [ooIdentity () (Correspondence.identViolFeature back), markedness aerSigma,
   ioFaith (Correspondence.identViolFeature back)]

/-- The paradigms of (16) pair the base *L[a]rry* or *L[æ]rry* with the diminutive *L[a]r* or
*L[æ]r*, from the inputs `/læri/` and `/læri + TRUNC/`. -/
def cand : Cand4 → Correspondence Role Seg
  | .a => paradigm [.l, .ae, .r, .i] [.l, .a, .r, .i] [.l, .ae, .r, .i] [.l, .a, .r]
      (diagonalPairs 4) (diagonalPairs 3) (diagonalPairs 3)
  | .b => paradigm [.l, .ae, .r, .i] [.l, .a, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r]
      (diagonalPairs 4) (diagonalPairs 3) (diagonalPairs 3)
  | .c => paradigm [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .a, .r]
      (diagonalPairs 4) (diagonalPairs 3) (diagonalPairs 3)
  | .d => paradigm [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r]
      (diagonalPairs 4) (diagonalPairs 3) (diagonalPairs 3)

/-- In (16) and (29), under recursive evaluation the underapplication paradigm
*L[æ]rry ~ L[æ]r* wins, since overapplication in the base costs an IO-IDENT violation in the
dominant recursion. -/
theorem underapplication :
    (tableau cand {.a, .b, .c, .d} recursive ranking ()).optimal = {.d} := by decide

/-- Without recursion, overapplication in the base *L[a]rry ~ L[a]r* wins, since it satisfies
OO-Identity and `*ær]σ` at the cost of low-ranked IO-Faith only. -/
theorem overapplication_nonrecursive :
    (tableau cand {.a, .b, .c, .d} nonrecursive ranking ()).optimal = {.a} := by decide

end English

/-! ### Sundanese nasal harmony (Ch. 3)

Nasality is allophonic — nasal after a nasal segment, oral elsewhere — by
`*NVORAL >> *VNAS >> IO-IDENT[NAS]` (48); it overapplies in the infixed plural
*ɲĩãr ~ ɲ-ãl-ĩãr* and applies normally in *dəhəs ~ d-um-ə̃hə̃s* under the single ranking
`*NVORAL >> OO-IDENT[NAS] >> *VNAS >> IO-IDENT[NAS]` (58); data from [cohn-1990]. -/

namespace Sundanese

/-- Sundanese segments by the features the constraints read, laryngeals being transparent
to nasal spread. -/
inductive Seg
  | nasalC | oralC | laryngeal | oralV | nasalV
  deriving DecidableEq, Repr

/-- Nasality. -/
def nasal : Seg → Bool
  | .nasalC | .nasalV => true
  | _ => false

/-- `*NVORAL` (45) bans an oral vowel in post-nasal context, laryngeals skipped. -/
def nvOral : List Seg → ℕ :=
  go false
where
  /-- `postNasal` records whether the last non-laryngeal segment was nasal. -/
  go (postNasal : Bool) : List Seg → ℕ
    | [] => 0
    | .oralV :: rest => (if postNasal then 1 else 0) + go false rest
    | .laryngeal :: rest => go postNasal rest
    | s :: rest => go (nasal s) rest

/-- `*VNAS` (44) bans a nasal vowel. -/
def vNas (w : List Seg) : ℕ := w.count .nasalV

/-- The ranking (58), `*NVORAL >> OO-IDENT[NAS] >> *VNAS >> IO-IDENT[NAS]`. -/
def ranking : List (Unit → ParadigmConstraint Seg) :=
  [markedness nvOral, ooIdentity () (Correspondence.identViolFeature nasal), markedness vNas,
   ioFaith (Correspondence.identViolFeature nasal)]

/-- The four rich inputs of (47) for *ŋãtur* 'arrange', which are also its candidates
*ŋatur, ŋatũr, ŋãtũr, ŋãtur*. -/
def inputs : List (List Seg) :=
  [[.nasalC, .oralV, .oralC, .oralV, .oralC], [.nasalC, .nasalV, .oralC, .oralV, .oralC],
   [.nasalC, .oralV, .oralC, .nasalV, .oralC], [.nasalC, .nasalV, .oralC, .nasalV, .oralC]]

/-- The output candidates of (47), by their vowels. -/
def word : Cand4 → List Seg
  | .a => [.nasalC, .oralV, .oralC, .oralV, .oralC]
  | .b => [.nasalC, .oralV, .oralC, .nasalV, .oralC]
  | .c => [.nasalC, .nasalV, .oralC, .nasalV, .oralC]
  | .d => [.nasalC, .nasalV, .oralC, .oralV, .oralC]

/-- In (47), whatever the input's vowels, `*NVORAL >> *VNAS >> IO-IDENT[NAS]` selects
*ŋãtur*, so markedness decides allophony over the rich input. -/
theorem allophony : ∀ input ∈ inputs,
    (Tableau.ofList {.a, .b, .c, .d}
      [Constraint.comap word nvOral, Constraint.comap word vNas,
       fun w ↦ (Correspondence.parallel input (word w)).identViolFeature nasal .lhs .rhs]).optimal =
      {Cand4.d} := by
  decide

/-- The correspondence of the plural's input `/ãl + ɲĩãr/` with its infixed output
`ɲ-ãl-ĩãr` places the affix's segments after the root-initial nasal. -/
def infixIO : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (3, 3), (4, 4), (5, 5)]

/-- The OO correspondence of *ɲĩãr* with *ɲ-ãl-ĩãr*: the root around the infix. -/
def infixOO : List (ℕ × ℕ) := [(0, 0), (1, 3), (2, 4), (3, 5)]

/-- The paradigms of (52) pair the base *ɲiar* or *ɲĩãr* with the plural *ɲ-ãl-iar* or
*ɲ-ãl-ĩãr*, from the inputs `/ɲĩãr/` and `/ãl + ɲĩãr/`. -/
def plural : Cand4 → Correspondence Role Seg
  | .a => paradigm [.nasalC, .nasalV, .nasalV, .oralC] [.nasalC, .oralV, .oralV, .oralC]
      [.nasalV, .oralC, .nasalC, .nasalV, .nasalV, .oralC]
      [.nasalC, .nasalV, .oralC, .oralV, .oralV, .oralC] (diagonalPairs 4) infixIO infixOO
  | .b => paradigm [.nasalC, .nasalV, .nasalV, .oralC] [.nasalC, .oralV, .oralV, .oralC]
      [.nasalV, .oralC, .nasalC, .nasalV, .nasalV, .oralC]
      [.nasalC, .nasalV, .oralC, .nasalV, .nasalV, .oralC] (diagonalPairs 4) infixIO infixOO
  | .c => paradigm [.nasalC, .nasalV, .nasalV, .oralC] [.nasalC, .nasalV, .nasalV, .oralC]
      [.nasalV, .oralC, .nasalC, .nasalV, .nasalV, .oralC]
      [.nasalC, .nasalV, .oralC, .oralV, .oralV, .oralC] (diagonalPairs 4) infixIO infixOO
  | .d => paradigm [.nasalC, .nasalV, .nasalV, .oralC] [.nasalC, .nasalV, .nasalV, .oralC]
      [.nasalV, .oralC, .nasalC, .nasalV, .nasalV, .oralC]
      [.nasalC, .nasalV, .oralC, .nasalV, .nasalV, .oralC] (diagonalPairs 4) infixIO infixOO

/-- In (52) nasal spread overapplies in the plural: *ɲĩãr ~ ɲ-ãl-ĩãr* wins, its root vowels
nasal in oral context to match the base. -/
theorem overapplication :
    (tableau plural {.a, .b, .c, .d} recursive ranking ()).optimal = {.d} := by decide

/-- The OO correspondence of *dəhəs* with *d-um-əhəs*. -/
def umOO : List (ℕ × ℕ) := [(0, 0), (1, 3), (2, 4), (3, 5), (4, 6)]

/-- The correspondence of `/ũm + dəhəs/` with *d-um-əhəs*. -/
def umIO : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (3, 3), (4, 4), (5, 5), (6, 6)]

/-- The paradigms of (55) share the canonical base *dəhəs*, and the infixed word's vowels are
oral or nasal in the infix and in the root. -/
def approach : Cand4 → Correspondence Role Seg
  | .a => paradigm base base input
      [.oralC, .oralV, .nasalC, .oralV, .laryngeal, .oralV, .oralC] (diagonalPairs 5) umIO umOO
  | .b => paradigm base base input
      [.oralC, .nasalV, .nasalC, .oralV, .laryngeal, .oralV, .oralC] (diagonalPairs 5) umIO umOO
  | .c => paradigm base base input
      [.oralC, .oralV, .nasalC, .nasalV, .laryngeal, .nasalV, .oralC] (diagonalPairs 5) umIO umOO
  | .d => paradigm base base input
      [.oralC, .nasalV, .nasalC, .nasalV, .laryngeal, .nasalV, .oralC] (diagonalPairs 5) umIO umOO
where
  base : List Seg := [.oralC, .oralV, .laryngeal, .oralV, .oralC]
  input : List Seg := [.nasalV, .nasalC, .oralC, .oralV, .laryngeal, .oralV, .oralC]

/-- In (55) harmony applies normally under a nasal affix, *dəhəs ~ d-um-ə̃hə̃s*: OO-Identity
gives way to `*NVORAL`, and `*VNAS` keeps the infix vowel oral. -/
theorem normalApplication :
    (tableau approach {.a, .b, .c, .d} recursive ranking ()).optimal = {.c} := by decide

/-- The paradigms of (56) and (57) set the base *də̃hə̃s*, which would overapply to restore
identity, against the canonical *dəhəs*. -/
def baseChoice : Cand3 → Correspondence Role Seg
  | .a => paradigm approach.base [.oralC, .nasalV, .laryngeal, .nasalV, .oralC] approach.input
      [.oralC, .oralV, .nasalC, .nasalV, .laryngeal, .nasalV, .oralC] (diagonalPairs 5) umIO umOO
  | _ => approach .c

/-- In (56) the base cannot misapply, since its `*VNAS` marks fall in the dominant recursion. -/
theorem base_priority :
    (tableau baseChoice {.a, .b} recursive ranking ()).optimal = {.b} := by decide

/-- In (57) the non-recursive tally wrongly prefers the overapplying base, which satisfies
`*NVORAL` and OO-Identity outright. -/
theorem base_overapplies_nonrecursive :
    (tableau baseChoice {.a, .b} nonrecursive ranking ()).optimal = {.a} := by decide

end Sundanese

/-! ### Tiberian Hebrew truncation (Ch. 4)

Jussive/2fs truncation invokes one OO relation, imperative truncation another (§4.6.3).
Epenthesis, driven by `*COMPLEX-CODA >> IO-DEP` (85), underapplies in jussives under
`OOJ-DEP >> *COMPLEX-CODA` (89) except into rising-sonority clusters, `SON-CON >>
OOJ-DEP` (93); post-vocalic spirantization, driven by `*V-STOP >> *SPIR >>
IO-IDENT[CONT]` (115), underapplies in 2fs stems and applies normally in imperatives,
`OOJ-ID[CONT] >> *V-STOP >> *SPIR >> OOI-ID[CONT], IO-ID[CONT]` (137). -/

namespace Hebrew

/-- The two OO relations of the grammar, of jussive/2fs truncation and of imperative
truncation. -/
inductive Relation
  | jussive | imperative
  deriving DecidableEq, Repr

/-- Segments by the classes the constraints read, the sonority scale of fn. 64 and the
stop/spirant contrast. -/
inductive Seg
  | vowel | glide | guttural | liquid | nasal | sibilant | spirant | stop
  deriving DecidableEq, Repr

/-- Sonority (fn. 64) ranks vowel > glide > liquid > nasal > fricative > stop. -/
def sonority : Seg → ℕ
  | .vowel => 6
  | .glide | .guttural => 5
  | .liquid => 4
  | .nasal => 3
  | .sibilant | .spirant => 2
  | .stop => 1

/-- `[±continuant]` on the alternating obstruents. -/
def continuant : Seg → Option Bool
  | .stop => some false
  | .spirant => some true
  | _ => none

/-- The word-final consonant cluster, if any: a complex coda. -/
def finalCluster : List Seg → Option (Seg × Seg)
  | [] => none
  | [_] => none
  | [x, y] => if x ≠ .vowel ∧ y ≠ .vowel then some (x, y) else none
  | _ :: rest => finalCluster rest

/-- `*COMPLEX-CODA` (84). -/
def complexCoda (w : List Seg) : ℕ := if (finalCluster w).isSome then 1 else 0

/-- `SON-CON` (91): a coda that rises in sonority. -/
def sonCon (w : List Seg) : ℕ :=
  match finalCluster w with
  | some (x, y) => if sonority x < sonority y then 1 else 0
  | none => 0

/-- In the markedness relation TETRU makes emerge (§4.3.2), `SON-CON` marks a subset of the
codas `*COMPLEX-CODA` marks. -/
theorem sonCon_le_complexCoda (w : List Seg) : sonCon w ≤ complexCoda w := by
  unfold sonCon complexCoda
  cases finalCluster w with
  | none => simp
  | some p =>
    obtain ⟨x, y⟩ := p
    show (if sonority x < sonority y then 1 else 0) ≤ 1
    split <;> omega

/-- `*V-STOP` (112): a post-vocalic stop. -/
def vStop : List Seg → ℕ
  | .vowel :: .stop :: rest => 1 + vStop (.stop :: rest)
  | _ :: rest => vStop rest
  | [] => 0

/-- `*SPIR` (111). -/
def spir (w : List Seg) : ℕ := w.count .spirant

/-- The epenthesis hierarchy of (93), `SON-CON >> OOJ-DEP >> *COMPLEX-CODA >> IO-DEP`. -/
def epenthesis : List (Relation → ParadigmConstraint Seg) :=
  [markedness sonCon, ooIdentity .jussive Correspondence.depViol, markedness complexCoda,
   ioFaith Correspondence.depViol]

/-- The spirantization hierarchy of (137). -/
def spirantization : List (Relation → ParadigmConstraint Seg) :=
  [ooIdentity .jussive (Correspondence.identViolFeature continuant), markedness vStop,
   markedness spir, ooIdentity .imperative (Correspondence.identViolFeature continuant),
   ioFaith (Correspondence.identViolFeature continuant)]

/-- The jussive paradigms of (87), from `/ya-šbē/` and `/ya-šbē-TRUNC/`, pair the base
*yi.šə.bē* or *yiš.bē* with the jussive *yi.šeb* or *yišb*. -/
def captive : Cand4 → Correspondence Role Seg
  | .a => paradigm input [.glide, .vowel, .sibilant, .vowel, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .vowel, .stop] epenthetic epenthetic (diagonalPairs 5)
  | .b => paradigm input [.glide, .vowel, .sibilant, .vowel, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .stop] epenthetic (diagonalPairs 4)
      [(0, 0), (1, 1), (2, 2), (4, 3)]
  | .c => paradigm input [.glide, .vowel, .sibilant, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .vowel, .stop] (diagonalPairs 5) epenthetic
      [(0, 0), (1, 1), (2, 2), (3, 4)]
  | .d => paradigm input [.glide, .vowel, .sibilant, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .stop] (diagonalPairs 5) (diagonalPairs 4) (diagonalPairs 4)
where
  input : List Seg := [.glide, .vowel, .sibilant, .stop, .vowel]
  /-- An IO correspondence with a vowel epenthesized after the third segment. -/
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4), (4, 5)]

/-- In (87) epenthesis underapplies in *yiš.bē ~ yišb* 'take captive', the complex coda kept
to give every jussive segment a base correspondent. -/
theorem epenthesis_underapplies :
    (tableau captive {.a, .b, .c, .d} recursive epenthesis .jussive).optimal = {.d} := by
  decide

/-- In (88) the non-recursive tally prefers epenthesis overapplying in the base,
*yi.šə.bē ~ yi.šeb*. -/
theorem epenthesis_overapplies_nonrecursive :
    (tableau captive {.a, .b, .c, .d} nonrecursive epenthesis .jussive).optimal = {.a} := by
  decide

/-- The paradigms of (92), from `/ya-glē/`, pair the base *yi.ɣə.lē* or *yiɣ.lē* with the
jussive *yi.ɣel* or *yiɣl*. -/
def uncover : Cand3 → Correspondence Role Seg
  | .a => paradigm input [.glide, .vowel, .spirant, .vowel, .liquid, .vowel] input
      [.glide, .vowel, .spirant, .vowel, .liquid] captive.epenthetic captive.epenthetic
      (diagonalPairs 5)
  | .b => paradigm input [.glide, .vowel, .spirant, .liquid, .vowel] input
      [.glide, .vowel, .spirant, .vowel, .liquid] (diagonalPairs 5) captive.epenthetic
      [(0, 0), (1, 1), (2, 2), (3, 4)]
  | .c => paradigm input [.glide, .vowel, .spirant, .liquid, .vowel] input
      [.glide, .vowel, .spirant, .liquid] (diagonalPairs 5) (diagonalPairs 4) (diagonalPairs 4)
where
  input : List Seg := [.glide, .vowel, .spirant, .liquid, .vowel]

/-- In (92), by TETRU, epenthesis applies normally into a rising-sonority cluster,
*yiɣ.lē ~ yi.ɣel* 'uncover', with `SON-CON` outranking OOJ-DEP, while the overapplying base
loses in the dominant recursion. -/
theorem tetru :
    (tableau uncover {.a, .b, .c} recursive epenthesis .jussive).optimal = {.b} := by decide

/-- The 2fs paradigms of (118), from `/šamaʕ-tī/` and its truncation, have a stop or a spirant
as the base's coronal and as the 2fs stem's after the epenthetic vowel. -/
def heard : Cand3 → Correspondence Role Seg
  | .a => paradigm input (stem .spirant .vowel) input (stem .vowel .spirant) (diagonalPairs 7)
      truncated truncated
  | .b => paradigm input (stem .stop .vowel) input (stem .vowel .spirant) (diagonalPairs 7)
      truncated truncated
  | .c => paradigm input (stem .stop .vowel) input (stem .vowel .stop) (diagonalPairs 7)
      truncated truncated
where
  /-- *šāmaʕ* followed by two segments. -/
  stem (x y : Seg) : List Seg := [.sibilant, .vowel, .nasal, .vowel, .guttural, x, y]
  input : List Seg := stem .stop .vowel
  /-- The correspondence of *šāmaʕtī* with *šāmaʕat* truncates the final vowel and
  epenthesizes a vowel before the stop. -/
  truncated : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 6)]

/-- In (118) spirantization underapplies in *šāmaʕtī ~ šāmaʕat* 'I/you (fs) heard', the
post-vocalic stop matching the base's. -/
theorem spirantization_underapplies :
    (tableau heard {.a, .b, .c} recursive spirantization .jussive).optimal = {.c} := by
  decide

/-- In (119) the non-recursive tally prefers spirantization overapplying in the base. -/
theorem spirantization_overapplies_nonrecursive :
    (tableau heard {.a, .b, .c} nonrecursive spirantization .jussive).optimal = {.a} := by
  decide

/-- The imperative paradigms of (135), from `/ya-ktōb/`, pair the base *yikθōβ* or *yixtōβ* with
the imperative *kəθōβ* or *xətōβ*. -/
def write : Cand3 → Correspondence Role Seg
  | .a => paradigm input [.glide, .vowel, .stop, .spirant, .vowel, .spirant] input
      [.stop, .vowel, .spirant, .vowel, .spirant] (diagonalPairs 6) imperativeIO imperativeOO
  | .b => paradigm input [.glide, .vowel, .spirant, .stop, .vowel, .spirant] input
      [.spirant, .vowel, .stop, .vowel, .spirant] (diagonalPairs 6) imperativeIO imperativeOO
  | .c => paradigm input [.glide, .vowel, .spirant, .stop, .vowel, .spirant] input
      [.stop, .vowel, .spirant, .vowel, .spirant] (diagonalPairs 6) imperativeIO imperativeOO
where
  input : List Seg := [.glide, .vowel, .stop, .stop, .vowel, .stop]
  /-- The imperative keeps the root; its second vowel is epenthetic. -/
  imperativeIO : List (ℕ × ℕ) := [(2, 0), (3, 2), (4, 3), (5, 4)]
  imperativeOO : List (ℕ × ℕ) := [(2, 0), (3, 2), (4, 3), (5, 4)]

/-- In (135) spirantization applies normally in the imperative *yixtōβ ~ kəθōβ* 'write'
under the same ranking (137), the imperative's OO-Identity ranked below the spirantization
constraints. -/
theorem imperative_normalApplication :
    (tableau write {.a, .b, .c} recursive spirantization .imperative).optimal = {.c} := by
  decide

end Hebrew

end Benua1997
