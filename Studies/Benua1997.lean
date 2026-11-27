module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Transderivational
public import Linglib.Phonology.Segmental.Sonority.Sequencing
public import Linglib.Phonology.Segmental.NasalCompatibility
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Benua 1997: transderivational identity

Benua holds a derived word identical to its base by constraints on an output–output
correspondence, ranked in one hierarchy with markedness and each word's faithfulness to its input,
and evaluates the two words recursively, the base above the derived word
(`OptimalityTheory.Transderivational`). Recursion makes underapplication optimal, as in
[*L[æ]rry ~ L[æ]r*](##English.underapplication), keeps a base from overapplying to restore
identity ([Sundanese](##Sundanese.base_priority)), and stops short of highly marked structure
([TETRU](##Hebrew.tetru)); two truncations differ only in [the rank of their identity
constraints](##Hebrew.imperative_normalApplication).

## Implementation notes

* The Sundanese segments are those of the PHOIBLE chart for the printed symbols, and the
  laryngeals, transparent to nasal spread, are the glottal class of
  `Phonology.NasalCompatibility`. The Tiberian Hebrew segments are the classes the constraints
  read, sonority class and continuancy, with the sibilants apart because \*SPIR bans only
  non-strident fricatives; vowel quality is not represented there.
* Each OO relation is the one the IO relations induce (`Transderivational.paradigm`), the
  Sundanese affixes preceding the root in the input; in every tableau it is the relation Benua
  draws.
* OO-Identity is vacuous at the base, a simplex word (p. 35 fn. 25); the relation of the Hebrew
  imperfective's prefix is ignored, as in the paper (p. 108 fn. 61).
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

open OptimalityTheory Transderivational
open OptimalityTheory.Correspondence (diagonalPairs)

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
  [ooIdentity () (Correspondence.Coindexation.identViolFeature back), markedness aerSigma,
   ioFaith (Correspondence.Coindexation.identViolFeature back)]

/-- The paradigms of (16) pair the base *L[a]rry* or *L[æ]rry* with the diminutive *L[a]r* or
*L[æ]r*, from the inputs `/læri/` and `/læri + TRUNC/`. -/
def cand : Cand4 → Correspondence.Coindexation Role Seg
  | .a => paradigm [.l, .ae, .r, .i] [.l, .a, .r, .i] [.l, .ae, .r, .i] [.l, .a, .r]
      (diagonalPairs 4) (diagonalPairs 3)
  | .b => paradigm [.l, .ae, .r, .i] [.l, .a, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r]
      (diagonalPairs 4) (diagonalPairs 3)
  | .c => paradigm [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .a, .r]
      (diagonalPairs 4) (diagonalPairs 3)
  | .d => paradigm [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r, .i] [.l, .ae, .r]
      (diagonalPairs 4) (diagonalPairs 3)

/-- The neutralisation underapplies in *L[æ]rry ~ L[æ]r* ((16), (29)): the overapplying
*L[a]rry ~ L[a]r*, which satisfies OO-Identity and `*ær]σ`, loses in the base's recursion. -/
theorem underapplication :
    Constraint.evalOn cand {.a, .b, .c, .d} (recursive ranking ()) = {.d} := by decide

-- p. 35
theorem overapplication_nonrecursive :
    Constraint.evalOn cand {.a, .b, .c, .d} (nonrecursive ranking ()) = {.a} := by decide

end English

/-! ### Sundanese nasal harmony (Ch. 3)

Nasality is allophonic, nasal after a nasal segment and oral elsewhere, by
`*NVORAL >> *VNAS >> IO-IDENT[NAS]` (44); it overapplies in the infixed plural
*ɲĩãr ~ ɲ-ãl-ĩãr* and applies normally in *dɤhɤs ~ d-um-ɤ̃hɤ̃s* under the single ranking
`*NVORAL >> OO-IDENT[NAS] >> *VNAS >> IO-IDENT[NAS]` (51); data from [cohn-1990]. -/

namespace Sundanese

open Phonology

/-- The segment [ŋ]. -/
def ŋ : Segment := .ofChart .«ŋ»
/-- The segment [ɲ]. -/
def «ɲ» : Segment := .ofChart .«ɲ»
/-- The segment [m]. -/
def m : Segment := .ofChart .«m»
/-- The segment [t]. -/
def t : Segment := .ofChart .«t»
/-- The segment [d]. -/
def d : Segment := .ofChart .«d»
/-- The segment [s]. -/
def s : Segment := .ofChart .«s»
/-- The segment [r]. -/
def r : Segment := .ofChart .«r»
/-- The segment [l]. -/
def l : Segment := .ofChart .«l»
/-- The segment [h]. -/
def h : Segment := .ofChart .«h»
/-- The segment [a]. -/
def a : Segment := .ofChart .«a»
/-- The segment [i]. -/
def i : Segment := .ofChart .«i»
/-- The segment [u]. -/
def u : Segment := .ofChart .«u»
/-- The segment [ɤ]. -/
def «ɤ» : Segment := .ofChart .«ɤ»
/-- The segment [ã]. -/
def «ã» : Segment := a.setFeature .nasal true
/-- The segment [ĩ]. -/
def «ĩ» : Segment := i.setFeature .nasal true
/-- The segment [ũ]. -/
def «ũ» : Segment := u.setFeature .nasal true
/-- The segment [ɤ̃]. -/
def «ɤ̃» : Segment := «ɤ».setFeature .nasal true

/-- (33): the laryngeals are transparent to nasal spread, and the constraint on post-nasal
vowels reads a word without them. -/
def IsSupralaryngeal (x : Segment) : Prop := NasalCompatibility.ofSegment x ≠ .glottal

instance : DecidablePred IsSupralaryngeal := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- A nasal vowel. -/
def IsNasalVowel (x : Segment) : Prop := x.IsVowel ∧ x .nasal = true

instance : DecidablePred IsNasalVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- `*NVORAL` (41) counts the oral vowels in post-nasal context: the vowels that are not nasal
and whose nearest preceding segment other than a laryngeal is nasal. -/
def nvOral (w : List Segment) : ℕ :=
  let v := w.filter fun x : Segment ↦ IsSupralaryngeal x
  (v.zip v.tail).countP fun (x, y) ↦ x .nasal = true ∧ y.IsVowel ∧ ¬ y .nasal = true

/-- `*VNAS` (40) counts the nasal vowels. -/
def vNas (w : List Segment) : ℕ := w.countP fun x : Segment ↦ IsNasalVowel x

-- (33): a word and the word without its laryngeals have the same oral vowels in post-nasal context
theorem nvOral_filter (w : List Segment) :
    nvOral (w.filter fun x : Segment ↦ IsSupralaryngeal x) = nvOral w := by
  simp [nvOral, List.filter_filter]

/-- The ranking (51), `*NVORAL >> OO-IDENT[NAS] >> *VNAS >> IO-IDENT[NAS]`. -/
def ranking : List (Unit → ParadigmConstraint Segment) :=
  [markedness nvOral,
   ooIdentity () (Correspondence.Coindexation.identViolFeature fun x : Segment ↦ x .nasal),
   markedness vNas,
   ioFaith (Correspondence.Coindexation.identViolFeature fun x : Segment ↦ x .nasal)]

/-- The four rich inputs of (43) for *ŋãtur* 'arrange', `/ŋatur/`, `/ŋãtur/`, `/ŋatũr/` and
`/ŋãtũr/`. -/
def inputs : List (List Segment) :=
  [[ŋ, a, t, u, r], [ŋ, «ã», t, u, r], [ŋ, a, t, «ũ», r], [ŋ, «ã», t, «ũ», r]]

/-- The output candidates of (43), *ŋatur*, *ŋatũr*, *ŋãtũr* and *ŋãtur*. -/
def word : Cand4 → List Segment
  | .a => [ŋ, a, t, u, r]
  | .b => [ŋ, a, t, «ũ», r]
  | .c => [ŋ, «ã», t, «ũ», r]
  | .d => [ŋ, «ã», t, u, r]

-- (43)
theorem allophony : ∀ input ∈ inputs,
    Constraint.eval {.a, .b, .c, .d}
      [Constraint.comap word nvOral, Constraint.comap word vNas,
       fun w ↦ (Correspondence.Coindexation.parallel input (word w)).identViolFeature
         (fun x : Segment ↦ x .nasal) .lhs .rhs] =
      {Cand4.d} := by
  decide +kernel

/-- The correspondence of the plural's input `/ãl + ɲĩãr/` with its infixed output
`ɲ-ãl-ĩãr` places the affix's segments after the root-initial nasal. -/
def infixIO : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (3, 3), (4, 4), (5, 5)]

/-- The paradigms of (48) pair the base *ɲiar* or *ɲĩãr* with the plural *ɲ-ãl-iar* or
*ɲ-ãl-ĩãr*, from the inputs `/ɲĩãr/` and `/ãl + ɲĩãr/`. -/
def plural : Cand4 → Correspondence.Coindexation Role Segment
  | .a => paradigm [«ɲ», «ĩ», «ã», r] [«ɲ», i, a, r] [«ã», l, «ɲ», «ĩ», «ã», r]
      [«ɲ», «ã», l, i, a, r] (diagonalPairs 4) infixIO 2
  | .b => paradigm [«ɲ», «ĩ», «ã», r] [«ɲ», i, a, r] [«ã», l, «ɲ», «ĩ», «ã», r]
      [«ɲ», «ã», l, «ĩ», «ã», r] (diagonalPairs 4) infixIO 2
  | .c => paradigm [«ɲ», «ĩ», «ã», r] [«ɲ», «ĩ», «ã», r] [«ã», l, «ɲ», «ĩ», «ã», r]
      [«ɲ», «ã», l, i, a, r] (diagonalPairs 4) infixIO 2
  | .d => paradigm [«ɲ», «ĩ», «ã», r] [«ɲ», «ĩ», «ã», r] [«ã», l, «ɲ», «ĩ», «ã», r]
      [«ɲ», «ã», l, «ĩ», «ã», r] (diagonalPairs 4) infixIO 2

-- (48)
theorem overapplication :
    Constraint.evalOn plural {.a, .b, .c, .d} (recursive ranking ()) = {.d} := by
  decide +kernel

/-- The correspondence of `/ũm + dɤhɤs/` with *d-um-ɤhɤs*. -/
def umIO : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (3, 3), (4, 4), (5, 5), (6, 6)]

/-- The paradigms of (51) share the canonical base *dɤhɤs*, and the infixed word's vowels are
oral or nasal in the infix and in the root: *d-um-ɤhɤs*, *d-ũm-ɤhɤs*, *d-um-ɤ̃hɤ̃s* and
*d-ũm-ɤ̃hɤ̃s*. -/
def approach : Cand4 → Correspondence.Coindexation Role Segment
  | .a => paradigm base base input [d, u, m, «ɤ», h, «ɤ», s] (diagonalPairs 5) umIO 2
  | .b => paradigm base base input [d, «ũ», m, «ɤ», h, «ɤ», s] (diagonalPairs 5) umIO 2
  | .c => paradigm base base input [d, u, m, «ɤ̃», h, «ɤ̃», s] (diagonalPairs 5) umIO 2
  | .d => paradigm base base input [d, «ũ», m, «ɤ̃», h, «ɤ̃», s] (diagonalPairs 5) umIO 2
where
  /-- The base *dɤhɤs*, faithful to its input. -/
  base : List Segment := [d, «ɤ», h, «ɤ», s]
  /-- The input `/ũm + dɤhɤs/`. -/
  input : List Segment := [«ũ», m, d, «ɤ», h, «ɤ», s]

-- (51)
theorem normalApplication :
    Constraint.evalOn approach {.a, .b, .c, .d} (recursive ranking ()) = {.c} := by
  decide +kernel

/-- The paradigms of (52) and (53) set the base *dɤ̃hɤ̃s*, which would overapply to restore
identity, against the canonical *dɤhɤs*. -/
def baseChoice : Cand2 → Correspondence.Coindexation Role Segment
  | .a => paradigm approach.base [d, «ɤ̃», h, «ɤ̃», s] approach.input
      [d, u, m, «ɤ̃», h, «ɤ̃», s] (diagonalPairs 5) umIO 2
  | .b => approach .c

/-- Misapplication in the base is never optimal (52): the base *dɤ̃hɤ̃s*, which overapplies nasal
harmony to restore identity, loses in the base's recursion, though summed evaluation selects it
(53). -/
theorem base_priority :
    Constraint.evalOn baseChoice {.a, .b} (recursive ranking ()) = {.b} := by decide +kernel

-- (53)
theorem base_overapplies_nonrecursive :
    Constraint.evalOn baseChoice {.a, .b} (nonrecursive ranking ()) = {.a} := by decide +kernel

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
  | some (x, y) => if sonority x < sonority y then 1 else 0
  | none => 0

theorem sonCon_eq_one_iff (w : List Seg) :
    sonCon w = 1 ↔ ∃ x y, finalCluster w = some (x, y) ∧ Sonority.PeaksAt sonority [x, y] 1 := by
  simp only [sonCon, Sonority.peaksAt_pair_one]
  split <;> simp_all

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
  [markedness sonCon, ooIdentity .jussive Correspondence.Coindexation.depViol,
   markedness complexCoda,
   ioFaith Correspondence.Coindexation.depViol]

/-- The spirantization hierarchy of (136). -/
def spirantization : List (Relation → ParadigmConstraint Seg) :=
  [ooIdentity .jussive (Correspondence.Coindexation.identViolFeature continuant), markedness vStop,
   markedness spir,
   ooIdentity .imperative (Correspondence.Coindexation.identViolFeature continuant),
   ioFaith (Correspondence.Coindexation.identViolFeature continuant)]

/-- The jussive paradigms of (82), from `/ya-šbē/` and `/ya-šbē-TRUNC/`, pair the base
*yi.šə.bē* or *yiš.bē* with the jussive *yi.šeb* or *yišb*. -/
def captive : Cand4 → Correspondence.Coindexation Role Seg
  | .a => paradigm input [.glide, .vowel, .sibilant, .vowel, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .vowel, .stop] epenthetic epenthetic
  | .b => paradigm input [.glide, .vowel, .sibilant, .vowel, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .stop] epenthetic (diagonalPairs 4)
  | .c => paradigm input [.glide, .vowel, .sibilant, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .vowel, .stop] (diagonalPairs 5) epenthetic
  | .d => paradigm input [.glide, .vowel, .sibilant, .stop, .vowel] input
      [.glide, .vowel, .sibilant, .stop] (diagonalPairs 5) (diagonalPairs 4)
where
  /-- The input `/ya-šbē/`. -/
  input : List Seg := [.glide, .vowel, .sibilant, .stop, .vowel]
  /-- An IO correspondence with a vowel epenthesized after the third segment. -/
  epenthetic : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 4), (4, 5)]

-- (82)
theorem epenthesis_underapplies :
    Constraint.evalOn captive {.a, .b, .c, .d} (recursive epenthesis .jussive) = {.d} := by
  decide

-- (83)
theorem epenthesis_overapplies_nonrecursive :
    Constraint.evalOn captive {.a, .d} (nonrecursive epenthesis .jussive) = {.a} := by
  decide

/-- The paradigms of (87), from `/ya-glē/`, pair the base *yi.ɣə.lē* or *yiɣ.lē* with the
jussive *yi.ɣel* or *yiɣl*. -/
def uncover : Cand3 → Correspondence.Coindexation Role Seg
  | .a => paradigm input [.glide, .vowel, .spirant, .vowel, .liquid, .vowel] input
      [.glide, .vowel, .spirant, .vowel, .liquid] captive.epenthetic captive.epenthetic
  | .b => paradigm input [.glide, .vowel, .spirant, .liquid, .vowel] input
      [.glide, .vowel, .spirant, .vowel, .liquid] (diagonalPairs 5) captive.epenthetic
  | .c => paradigm input [.glide, .vowel, .spirant, .liquid, .vowel] input
      [.glide, .vowel, .spirant, .liquid] (diagonalPairs 5) (diagonalPairs 4)
where
  /-- The input `/ya-glē/`, with the stop that surfaces as a spirant after the prefix vowel. -/
  input : List Seg := [.glide, .vowel, .stop, .liquid, .vowel]

/-- TETRU (87): epenthesis applies normally in *yiɣ.lē ~ yi.ɣel*, since the cluster *ɣl* that
underapplication would leave rises in sonority and SON-CON outranks OOJ-DEP, while the
overapplying base *yi.ɣə.lē* loses in the base's recursion. -/
theorem tetru :
    Constraint.evalOn uncover {.a, .b, .c} (recursive epenthesis .jussive) = {.b} := by
  decide

/-- The 2fs paradigms of (114), from `/šamaʕ-tī/` and its truncation, have a stop or a spirant
as the base's coronal and as the 2fs stem's after the epenthetic vowel. -/
def heard : Cand3 → Correspondence.Coindexation Role Seg
  | .a => paradigm input (stem .spirant .vowel) input (stem .vowel .spirant) (diagonalPairs 7)
      truncated
  | .b => paradigm input (stem .stop .vowel) input (stem .vowel .spirant) (diagonalPairs 7)
      truncated
  | .c => paradigm input (stem .stop .vowel) input (stem .vowel .stop) (diagonalPairs 7)
      truncated
where
  /-- *šāmaʕ* followed by two segments. -/
  stem (x y : Seg) : List Seg := [.sibilant, .vowel, .nasal, .vowel, .guttural, x, y]
  /-- The input `/šamaʕ-tī/`. -/
  input : List Seg := stem .stop .vowel
  /-- The 2fs stem's IO relation truncates the final vowel and epenthesizes a vowel before the
stop. -/
  truncated : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 6)]

-- (114)
theorem spirantization_underapplies :
    Constraint.evalOn heard {.a, .b, .c} (recursive spirantization .jussive) = {.c} := by
  decide

-- (115)
theorem spirantization_overapplies_nonrecursive :
    Constraint.evalOn heard {.a, .c} (nonrecursive spirantization .jussive) = {.a} := by
  decide

/-- The imperative paradigms of (134), from `/ya-ktōb/`, pair the base *yikθōβ* or *yixtōβ* with
the imperative *kəθōβ* or *xətōβ*. -/
def write : Cand3 → Correspondence.Coindexation Role Seg
  | .a => paradigm input [.glide, .vowel, .stop, .spirant, .vowel, .spirant] input
      [.stop, .vowel, .spirant, .vowel, .spirant] (diagonalPairs 6) imperativeIO
  | .b => paradigm input [.glide, .vowel, .spirant, .stop, .vowel, .spirant] input
      [.spirant, .vowel, .stop, .vowel, .spirant] (diagonalPairs 6) imperativeIO
  | .c => paradigm input [.glide, .vowel, .spirant, .stop, .vowel, .spirant] input
      [.stop, .vowel, .spirant, .vowel, .spirant] (diagonalPairs 6) imperativeIO
where
  /-- The input `/ya-ktōb/`. -/
  input : List Seg := [.glide, .vowel, .stop, .stop, .vowel, .stop]
  /-- The imperative keeps the root; its second vowel is epenthetic. -/
  imperativeIO : List (ℕ × ℕ) := [(2, 0), (3, 2), (4, 3), (5, 4)]

/-- Under the ranking (136) under which spirantization underapplies in 2fs stems, it applies
normally in the imperative *yixtōβ ~ kəθōβ* (134), whose OO relation's identity constraint
ranks below the spirantization constraints (§4.6.3). -/
theorem imperative_normalApplication :
    Constraint.evalOn write {.a, .b, .c} (recursive spirantization .imperative) =
      {.c} := by
  decide

/-- The imperative paradigms of (135), from `/ya-ydaʕ/`, pair the coalesced base *yēδaʕ* with
the imperative *δaʕ* or *daʕ*. -/
def know : Cand2 → Correspondence.Coindexation Role Seg
  | .a => paradigm input base input [.spirant, .vowel, .guttural] coalesced truncated
  | .b => paradigm input base input [.stop, .vowel, .guttural] coalesced truncated
where
  /-- The input `/ya-ydaʕ/`. -/
  input : List Seg := [.glide, .vowel, .glide, .stop, .vowel, .guttural]
  /-- The imperfective *yēδaʕ*. -/
  base : List Seg := [.glide, .vowel, .spirant, .vowel, .guttural]
  /-- The prefix vowel and the root glide coalesce. -/
  coalesced : List (ℕ × ℕ) := [(0, 0), (1, 1), (2, 1), (3, 2), (4, 3), (5, 4)]
  /-- The imperative keeps the root's last two consonants and its vowel. -/
  truncated : List (ℕ × ℕ) := [(3, 0), (4, 1), (5, 2)]

-- (135)
theorem imperative_initialStop :
    Constraint.evalOn know {.a, .b} (recursive spirantization .imperative) = {.b} := by
  decide

end Hebrew

end Benua1997
