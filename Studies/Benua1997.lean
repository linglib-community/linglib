module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Segmental.Sonority
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Benua 1997: transderivational identity

Benua holds a derived word identical to its base by constraints on an output–output
correspondence, ranked in one hierarchy with markedness and each word's faithfulness to its input.
Evaluated recursively, the base's copy of the hierarchy above the derived word's, [a paradigm
wins when its derived word wins among the paradigms whose base wins](##optimal_tableau_recursive).
Summed evaluation [never selects underapplication](##eq_zero_of_mem_optimal_nonrecursive),
recursion does ([*L[æ]rry ~ L[æ]r*](##English.underapplication)) unless it would leave a highly
marked structure ([TETRU](##Hebrew.tetru)), and two truncations differ only in [the rank of
their identity constraints](##Hebrew.imperative_normalApplication).

## Implementation notes

* Segments are the classes the constraints read: Sundanese by nasality, the laryngeals
  transparent to nasal spread; Tiberian Hebrew by sonority class and continuancy, with the
  sibilants apart because \*SPIR bans only non-strident fricatives. Vowel quality is not
  represented.
* OO-Identity is vacuous at the base, a simplex word with no OO relation of its own (p. 35
  fn. 25); the relation of the Hebrew imperfective's prefix is ignored, as in the paper (p. 108
  fn. 61).
* Summed evaluation adds each constraint's violations in the two words, as in tableaux (53),
  (83) and (115). The English summed tableau is not printed; p. 35 says it cannot select
  underapplication.
* Each Hebrew tableau runs the whole hierarchy (88) or (136), not only the constraints the
  paper's tableau prints.
* The scale SON-CON reads [refines the modal hierarchy](##Hebrew.coarsens_toSonority) but puts
  the gutturals with the glides, where [their features put them with the
  obstruents](##Hebrew.ofSegment_lt_guttural).
* English affix classes (Ch. 5), the guttural CODA-COND (§4.3.3), opacity (§4.4.3) and the serial
  alternatives (§3.5, §4.7) are not formalized.

## References

* [benua-1997]
* [cohn-1990]
-/

@[expose] public section

namespace Benua1997

open OptimalityTheory
open OptimalityTheory.Correspondence (diagonalPairs)

/-! ### Subparadigms and recursive evaluation -/

section Recursion

variable {α ρ L : Type*}

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
  /-- The violations the base incurs. -/
  atBase : Correspondence Role α → ℕ
  /-- The violations the derived word incurs. -/
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

/-- The copy of the hierarchy that evaluates the base of a paradigm bearing `r`. -/
def baseRecursion (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence Role α)) :=
  ranking.map fun k ↦ (k r).atBase

/-- The copy of the hierarchy that evaluates the derived word of a paradigm bearing `r`. -/
def derivedRecursion (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence Role α)) :=
  ranking.map fun k ↦ (k r).atDerived

/-- Recursive evaluation (§2.3.1) duplicates the hierarchy and ranks the base's copy above the
derived word's. -/
def recursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence Role α)) :=
  baseRecursion ranking r ++ derivedRecursion ranking r

/-- Summed evaluation tallies each constraint's violations over both words. -/
def nonrecursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence Role α)) :=
  ranking.map fun k c ↦ (k r).atBase c + (k r).atDerived c

/-- The tableau of the candidate paradigms `cand` labelled by `labels` under the constraints
`cs`. -/
def tableau (cand : L → Correspondence Role α) (labels : Finset L)
    (cs : List (Constraint (Correspondence Role α))) :=
  Tableau.ofList labels (cs.map (Constraint.comap cand))

variable {cand : L → Correspondence Role α} {labels : Finset L}
  {ranking : List (ρ → ParadigmConstraint α)} {r : ρ}

/-- Base priority is ranking priority (p. 46): the winners of recursive evaluation are the
derived word's winners among the paradigms whose base wins its own copy of the hierarchy. -/
theorem optimal_tableau_recursive :
    (tableau cand labels (recursive ranking r)).optimal =
      (tableau cand (tableau cand labels (baseRecursion ranking r)).optimal
        (derivedRecursion ranking r)).optimal := by
  rw [tableau, recursive, List.map_append, Tableau.optimal_ofList_append]
  rfl

theorem optimal_tableau_recursive_of_forall_eq
    (h : ∀ k ∈ ranking, ∀ x ∈ labels, ∀ y ∈ labels, (k r).atBase (cand x) = (k r).atBase (cand y)) :
    (tableau cand labels (recursive ranking r)).optimal =
      (Tableau.ofList labels (ranking.map fun k ↦ (k r).atDerived ∘ cand)).optimal := by
  rw [tableau, recursive, List.map_append, Tableau.optimal_ofList_append_of_forall_eq]
  · rw [derivedRecursion, List.map_map]
    rfl
  · simp only [baseRecursion, List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩ x hx y hy
    exact h k hk x hx y hy

/-- Without recursion underapplication is never optimal (pp. 35, 109): under summed evaluation, if
some paradigm satisfies the top constraints in both words, as overapplication satisfies
OO-Identity and the markedness constraint driving the process, so does every winner. -/
theorem eq_zero_of_mem_optimal_nonrecursive {top rest : List (ρ → ParadigmConstraint α)} {x y : L}
    (hy : y ∈ (tableau cand labels (nonrecursive (top ++ rest) r)).optimal) (hx : x ∈ labels)
    (h0 : ∀ k ∈ top, (k r).atBase (cand x) = 0 ∧ (k r).atDerived (cand x) = 0) :
    ∀ k ∈ top, (k r).atBase (cand y) = 0 ∧ (k r).atDerived (cand y) = 0 := by
  rw [tableau, nonrecursive, List.map_append, List.map_append] at hy
  have := Tableau.eq_zero_of_mem_optimal_ofList_append hy hx (by
    simp only [List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩
    simp [Constraint.comap, h0 k hk])
  intro k hk
  simpa [Constraint.comap] using this _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, rfl⟩)

end Recursion

/-- The candidate paradigms of a four-way tableau. -/
inductive Cand4
  | a | b | c | d
  deriving DecidableEq, Repr

/-- The candidate paradigms of a three-way tableau. -/
inductive Cand3
  | a | b | c
  deriving DecidableEq, Repr

/-- The candidate paradigms of a two-way tableau. -/
inductive Cand2
  | a | b
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

/-- The neutralisation underapplies in *L[æ]rry ~ L[æ]r* ((16), (29)): the overapplying
*L[a]rry ~ L[a]r*, which satisfies OO-Identity and `*ær]σ`, loses in the base's recursion. -/
theorem underapplication :
    (tableau cand {.a, .b, .c, .d} (recursive ranking ())).optimal = {.d} := by decide

-- p. 35
theorem overapplication_nonrecursive :
    (tableau cand {.a, .b, .c, .d} (nonrecursive ranking ())).optimal = {.a} := by decide

end English

/-! ### Sundanese nasal harmony (Ch. 3)

Nasality is allophonic, nasal after a nasal segment and oral elsewhere, by
`*NVORAL >> *VNAS >> IO-IDENT[NAS]` (44); it overapplies in the infixed plural
*ɲĩãr ~ ɲ-ãl-ĩãr* and applies normally in *dəhəs ~ d-um-ə̃hə̃s* under the single ranking
`*NVORAL >> OO-IDENT[NAS] >> *VNAS >> IO-IDENT[NAS]` (51); data from [cohn-1990]. -/

namespace Sundanese

/-- Sundanese segments by the features the constraints read, laryngeals being transparent
to nasal spread (33). -/
inductive Seg
  | nasalC | oralC | laryngeal | oralV | nasalV
  deriving DecidableEq, Repr

/-- Nasality. -/
def nasal : Seg → Bool
  | .nasalC | .nasalV => true
  | _ => false

/-- `*NVORAL` (41) bans an oral vowel in post-nasal context, laryngeals skipped. -/
def nvOral : List Seg → ℕ :=
  go false
where
  /-- `postNasal` records whether the last non-laryngeal segment was nasal. -/
  go (postNasal : Bool) : List Seg → ℕ
    | [] => 0
    | .oralV :: rest => (if postNasal then 1 else 0) + go false rest
    | .laryngeal :: rest => go postNasal rest
    | s :: rest => go (nasal s) rest

/-- `*VNAS` (40) bans a nasal vowel. -/
def vNas (w : List Seg) : ℕ := w.count .nasalV

/-- The ranking (51), `*NVORAL >> OO-IDENT[NAS] >> *VNAS >> IO-IDENT[NAS]`. -/
def ranking : List (Unit → ParadigmConstraint Seg) :=
  [markedness nvOral, ooIdentity () (Correspondence.identViolFeature nasal), markedness vNas,
   ioFaith (Correspondence.identViolFeature nasal)]

/-- The four rich inputs of (43) for *ŋãtur* 'arrange', which are also its candidates
*ŋatur, ŋatũr, ŋãtũr, ŋãtur*. -/
def inputs : List (List Seg) :=
  [[.nasalC, .oralV, .oralC, .oralV, .oralC], [.nasalC, .nasalV, .oralC, .oralV, .oralC],
   [.nasalC, .oralV, .oralC, .nasalV, .oralC], [.nasalC, .nasalV, .oralC, .nasalV, .oralC]]

/-- The output candidates of (43), by their vowels. -/
def word : Cand4 → List Seg
  | .a => [.nasalC, .oralV, .oralC, .oralV, .oralC]
  | .b => [.nasalC, .oralV, .oralC, .nasalV, .oralC]
  | .c => [.nasalC, .nasalV, .oralC, .nasalV, .oralC]
  | .d => [.nasalC, .nasalV, .oralC, .oralV, .oralC]

-- (43)
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

/-- The paradigms of (48) pair the base *ɲiar* or *ɲĩãr* with the plural *ɲ-ãl-iar* or
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

-- (48)
theorem overapplication :
    (tableau plural {.a, .b, .c, .d} (recursive ranking ())).optimal = {.d} := by decide

/-- The OO correspondence of *dəhəs* with *d-um-əhəs*. -/
def umOO : List (ℕ × ℕ) := [(0, 0), (1, 3), (2, 4), (3, 5), (4, 6)]

/-- The correspondence of `/ũm + dəhəs/` with *d-um-əhəs*. -/
def umIO : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (3, 3), (4, 4), (5, 5), (6, 6)]

/-- The paradigms of (51) share the canonical base *dəhəs*, and the infixed word's vowels are
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
  /-- The base *dəhəs*, faithful to its input. -/
  base : List Seg := [.oralC, .oralV, .laryngeal, .oralV, .oralC]
  /-- The input `/ũm + dəhəs/`. -/
  input : List Seg := [.nasalV, .nasalC, .oralC, .oralV, .laryngeal, .oralV, .oralC]

-- (51)
theorem normalApplication :
    (tableau approach {.a, .b, .c, .d} (recursive ranking ())).optimal = {.c} := by decide

/-- The paradigms of (52) and (53) set the base *də̃hə̃s*, which would overapply to restore
identity, against the canonical *dəhəs*. -/
def baseChoice : Cand2 → Correspondence Role Seg
  | .a => paradigm approach.base [.oralC, .nasalV, .laryngeal, .nasalV, .oralC] approach.input
      [.oralC, .oralV, .nasalC, .nasalV, .laryngeal, .nasalV, .oralC] (diagonalPairs 5) umIO umOO
  | .b => approach .c

-- (52)
theorem base_priority :
    (tableau baseChoice {.a, .b} (recursive ranking ())).optimal = {.b} := by decide

-- (53)
theorem base_overapplies_nonrecursive :
    (tableau baseChoice {.a, .b} (nonrecursive ranking ())).optimal = {.a} := by decide

end Sundanese

/-! ### Tiberian Hebrew truncation (Ch. 4)

Jussive/2fs truncation invokes one OO relation, imperative truncation another (§4.6.3).
Epenthesis, driven by `*COMPLEX-CODA >> IO-DEP` (80), underapplies in jussives under
`OOJ-DEP >> *COMPLEX-CODA` (84) except into rising-sonority clusters, `SON-CON >>
OOJ-DEP` (87); post-vocalic spirantization, driven by `*V-STOP >> *SPIR >>
IO-IDENT[CONT]` (111), underapplies in 2fs stems and applies normally in imperatives,
`OOJ-ID[CONT] >> *V-STOP >> *SPIR >> OOI-ID[CONT], IO-ID[CONT]` (136). -/

namespace Hebrew

/-- The two OO relations of the grammar, of jussive/2fs truncation and of imperative
truncation. -/
inductive Relation
  | jussive | imperative
  deriving DecidableEq, Repr

/-- Segments by the classes the constraints read: those of the sonority scale and the
stop/spirant contrast. -/
inductive Seg
  | vowel | glide | guttural | liquid | nasal | sibilant | spirant | stop
  deriving DecidableEq, Repr, Fintype

/-- The sonority scale vowel > glide > liquid > nasal > fricative > stop (p. 106, p. 110
fn. 62), with the gutturals among the glides (p. 115). -/
def sonority : Seg → ℕ
  | .vowel => 6
  | .glide | .guttural => 5
  | .liquid => 4
  | .nasal => 3
  | .sibilant | .spirant => 2
  | .stop => 1

open Phonology (Segment Sonority)

/-- The class of the modal hierarchy that a class falls in. -/
def Seg.toSonority : Seg → Sonority
  | .vowel => .vowel
  | .glide | .guttural => .glide
  | .liquid => .liquid
  | .nasal => .nasal
  | .sibilant | .spirant | .stop => .obstruent

theorem coarsens_toSonority : Sonority.Coarsens Seg.toSonority sonority := by
  unfold Sonority.Coarsens
  decide

theorem ofSegment_lt_guttural :
    ∀ g ∈ [Segment.ofChart .«ʔ», .ofChart .«h», .ofChart .«ʕ», .ofChart .«ħ»],
      Sonority.ofSegment g < Seg.guttural.toSonority := by
  decide +kernel

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

/-- `*COMPLEX-CODA` (79). -/
def complexCoda (w : List Seg) : ℕ := if (finalCluster w).isSome then 1 else 0

/-- `SON-CON` (86): a coda that rises in sonority. -/
def sonCon (w : List Seg) : ℕ :=
  match finalCluster w with
  | some (x, y) => if Sonority.profile sonority x y = .lt then 1 else 0
  | none => 0

-- pp. 49, 113
theorem sonCon_le_complexCoda (w : List Seg) : sonCon w ≤ complexCoda w := by
  grind [sonCon, complexCoda]

/-- `*V-STOP` (108): a post-vocalic stop. -/
def vStop : List Seg → ℕ
  | .vowel :: .stop :: rest => 1 + vStop (.stop :: rest)
  | _ :: rest => vStop rest
  | [] => 0

/-- `*SPIR` (107). -/
def spir (w : List Seg) : ℕ := w.count .spirant

/-- The epenthesis hierarchy of (88), `SON-CON >> OOJ-DEP >> *COMPLEX-CODA >> IO-DEP`. -/
def epenthesis : List (Relation → ParadigmConstraint Seg) :=
  [markedness sonCon, ooIdentity .jussive Correspondence.depViol, markedness complexCoda,
   ioFaith Correspondence.depViol]

/-- The spirantization hierarchy of (136). -/
def spirantization : List (Relation → ParadigmConstraint Seg) :=
  [ooIdentity .jussive (Correspondence.identViolFeature continuant), markedness vStop,
   markedness spir, ooIdentity .imperative (Correspondence.identViolFeature continuant),
   ioFaith (Correspondence.identViolFeature continuant)]

/-- The jussive paradigms of (82), from `/ya-šbē/` and `/ya-šbē-TRUNC/`, pair the base
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
  /-- The input `/ya-šbē/`. -/
  input : List Seg := [.glide, .vowel, .sibilant, .stop, .vowel]
  /-- An IO correspondence with a vowel epenthesized after the third segment. -/
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4), (4, 5)]

-- (82)
theorem epenthesis_underapplies :
    (tableau captive {.a, .b, .c, .d} (recursive epenthesis .jussive)).optimal = {.d} := by
  decide

-- (83)
theorem epenthesis_overapplies_nonrecursive :
    (tableau captive {.a, .d} (nonrecursive epenthesis .jussive)).optimal = {.a} := by
  decide

/-- The paradigms of (87), from `/ya-glē/`, pair the base *yi.ɣə.lē* or *yiɣ.lē* with the
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
  /-- The input `/ya-glē/`, with the stop that surfaces as a spirant after the prefix vowel. -/
  input : List Seg := [.glide, .vowel, .stop, .liquid, .vowel]

/-- TETRU (87): epenthesis applies normally in *yiɣ.lē ~ yi.ɣel*, since the cluster *ɣl* that
underapplication would leave rises in sonority and SON-CON outranks OOJ-DEP, while the
overapplying base *yi.ɣə.lē* loses in the base's recursion. -/
theorem tetru :
    (tableau uncover {.a, .b, .c} (recursive epenthesis .jussive)).optimal = {.b} := by decide

/-- The 2fs paradigms of (114), from `/šamaʕ-tī/` and its truncation, have a stop or a spirant
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
  /-- The input `/šamaʕ-tī/`. -/
  input : List Seg := stem .stop .vowel
  /-- The correspondence of *šāmaʕtī* with *šāmaʕat* truncates the final vowel and
  epenthesizes a vowel before the stop. -/
  truncated : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 6)]

-- (114)
theorem spirantization_underapplies :
    (tableau heard {.a, .b, .c} (recursive spirantization .jussive)).optimal = {.c} := by
  decide

-- (115)
theorem spirantization_overapplies_nonrecursive :
    (tableau heard {.a, .c} (nonrecursive spirantization .jussive)).optimal = {.a} := by
  decide

/-- The imperative paradigms of (134), from `/ya-ktōb/`, pair the base *yikθōβ* or *yixtōβ* with
the imperative *kəθōβ* or *xətōβ*. -/
def write : Cand3 → Correspondence Role Seg
  | .a => paradigm input [.glide, .vowel, .stop, .spirant, .vowel, .spirant] input
      [.stop, .vowel, .spirant, .vowel, .spirant] (diagonalPairs 6) imperativeIO imperativeOO
  | .b => paradigm input [.glide, .vowel, .spirant, .stop, .vowel, .spirant] input
      [.spirant, .vowel, .stop, .vowel, .spirant] (diagonalPairs 6) imperativeIO imperativeOO
  | .c => paradigm input [.glide, .vowel, .spirant, .stop, .vowel, .spirant] input
      [.stop, .vowel, .spirant, .vowel, .spirant] (diagonalPairs 6) imperativeIO imperativeOO
where
  /-- The input `/ya-ktōb/`. -/
  input : List Seg := [.glide, .vowel, .stop, .stop, .vowel, .stop]
  /-- The imperative keeps the root; its second vowel is epenthetic. -/
  imperativeIO : List (ℕ × ℕ) := [(2, 0), (3, 2), (4, 3), (5, 4)]
  /-- The root's segments in the imperfective correspond to theirs in the imperative. -/
  imperativeOO : List (ℕ × ℕ) := [(2, 0), (3, 2), (4, 3), (5, 4)]

/-- Under the ranking (136) under which spirantization underapplies in 2fs stems, it applies
normally in the imperative *yixtōβ ~ kəθōβ* (134), whose OO relation's identity constraint
ranks below the spirantization constraints (§4.6.3). -/
theorem imperative_normalApplication :
    (tableau write {.a, .b, .c} (recursive spirantization .imperative)).optimal = {.c} := by
  decide

/-- The imperative paradigms of (135), from `/ya-ydaʕ/`, pair the coalesced base *yēδaʕ* with
the imperative *δaʕ* or *daʕ*. -/
def know : Cand2 → Correspondence Role Seg
  | .a => paradigm input base input [.spirant, .vowel, .guttural] coalesced truncated
      truncatedOO
  | .b => paradigm input base input [.stop, .vowel, .guttural] coalesced truncated truncatedOO
where
  /-- The input `/ya-ydaʕ/`. -/
  input : List Seg := [.glide, .vowel, .glide, .stop, .vowel, .guttural]
  /-- The imperfective *yēδaʕ*. -/
  base : List Seg := [.glide, .vowel, .spirant, .vowel, .guttural]
  /-- The prefix vowel and the root glide coalesce. -/
  coalesced : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 1), (3, 2), (4, 3), (5, 4)]
  /-- The imperative keeps the root's last two consonants and its vowel. -/
  truncated : List (ℕ × ℕ) := [(3, 0), (4, 1), (5, 2)]
  /-- The imperfective's root segments correspond to theirs in the imperative. -/
  truncatedOO : List (ℕ × ℕ) := [(2, 0), (3, 1), (4, 2)]

-- (135)
theorem imperative_initialStop :
    (tableau know {.a, .b} (recursive spirantization .imperative)).optimal = {.b} := by decide

end Hebrew

end Benua1997
