module

public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Woolford1997
public import Linglib.Fragments.NezPerce.Case
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic

/-!
# Woolford (1997): Four-Way Case Systems: Ergative, Nominative, Objective and Accusative

This file derives the Case patterns of Nez Perce, Thangu and Kalkatungu from an inventory in which
ergative is a lexical Case and objects have two structural Cases, objective outside VP and
accusative inside it. A verb assigns at most $\#\text{arguments} - \#\text{lexical Cases} - 1$
accusatives, and [economy sends the highest caseless argument out of
VP](##mem_derivations_obligatory_iff), so that [a lexically Cased subject denies accusative to its
highest object](##getElem?_ne_acc_of_mem_derivations) in any language and, where accusative is
obligatory, [to no other](##count_acc_of_mem_derivations_obligatory). Whether a language assigns
ergative and dative obligatorily or optionally then [gives it its patterns](##rows_patterns), and
one clause of Kalkatungu is [ergative in morphology, nominative-accusative in agreement and
tripartite in abstract Case](##kalkatungu_alignments). With these lexical Cases as its input, [the
accusative rule of dependent case derives the same patterns](##map_value?_assign) wherever objects
can be nominative.

## Implementation notes

* Arguments are listed from the thematically highest down, so list position stands in for the
  height the economy condition measures and the path of a moved argument is its index.
* A row's Cases are in the Agent Goal Theme order of (22), not surface order. Its lexical Cases
  are the verb's choice and feed the prediction; its structural Cases are what is predicted.
* Null arguments in the rows of section 2 are given the Cases the verb's agreement and the paper's
  prose assign them, and `comment` says which. The first and second person subject pronouns of (40)
  and (41) show no ergative and are glossed for no Case; the rows take them as abstractly ergative,
  which is how p. 197 treats such pronouns.
* The prose before (27) also subtracts arguments with Case from a preposition, which (27) does not
  mention and no example tests.
* The strong interpretation of (19), on which a lexical subject denies accusative to every object,
  is `Assignment.lacking` on a clause with a lexical subject.
* `Params.deniedObject` is one Case per language, so Hindi's option of an objective *-ko* object
  (notes 17, 43) is not modelled. `Params.frames` has the classic type of ergative language, with
  nominative intransitive subjects (p. 190), which (60) does not list.
* `Case.position` is the tree (9), for the Cases of Nez Perce; note 21 expects dative subjects to
  raise as well.
* The comparison with dependent case is not the paper's, which cites no work on it. It runs the
  accusative rules with the paper's lexical ergative as input, where Marantz's own ergative is
  dependent, and it [does not extend to objective](##objective_not_elsewhere).

## Errata

* The conclusions (p. 223) say that languages not assigning Case inside VP, or doing so optionally,
  may manifest the nominative-accusative pattern. The sentence is about nominative-objective, as
  on p. 202: [without accusative the nominative-accusative pattern cannot
  arise](##nom_acc_notMem_lacking).
* P. 207 promises evidence in section 3 that some languages assign no structural accusative. Section
  3 has none: [Thangu's patterns do not depend on it](##thangu_accusative_irrelevant), as p. 216
  says, and Kalkatungu has accusative.
* Note 30 names an intransitive verb with a lexical Case as where the formula goes negative. So does
  [any verb whose every argument has lexical Case](##maxAcc_neg_iff), as in the ergative-dative
  pattern (18b) and in (63), so (27) must be read with a floor at zero.
* (8) cannot tell the attested (22A.4) from the starred (22B.7). Its dative and objective are both
  *-na*, the goal of (7) is *-na* glossed objective, (58) lists no dative, and both objects are
  third singular, so the prefix does not decide.
* (54) and (60) attribute Thangu's ditransitives to an obligatory dative, but [an optional dative
  gives the same patterns where accusative is lacking](##dative_not_forced).
* (32) is glossed 'bite' and translated 'hit'.

## TODO

* The passives (14) and (15), and the claim of section 1.2.1 that only structurally Cased objects
  passivize.
* The number agreement of (28) to (34), which reads the same two positions as (48).
* Accusative Case Blocking, the operation p. 208 proposes as the source of the formula.

## References

* [woolford-1997]
* [burzio-1986]
* [marantz-1991]
-/

@[expose] public section

namespace Woolford1997

open Morphology DependentCase Alignment

/-! ### The inventory of Cases -/

/-- The lexical Cases, which a verb assigns with a θ-role at D-structure: those of agents, of goals
and experiencers, and of themes. -/
inductive Lexical where
  | erg
  | dat
  | acc
  deriving DecidableEq, Repr, Fintype

/-- The core Cases of UG, ignoring the genitive: nominative and objective, structural and checked by
functional heads; accusative, structural and checked by a lexical head; and the lexical Cases. -/
inductive Case where
  /-- Structural, assigned or checked by Agr-S. -/
  | nom
  /-- Structural, assigned or checked by Agr-O. -/
  | obj
  /-- Structural, assigned or checked by V or P inside VP. -/
  | acc
  /-- A lexical Case. -/
  | lexical (l : Lexical)
  deriving DecidableEq, Repr, Fintype

/-- The ergative, a lexical Case. -/
@[match_pattern] abbrev Case.erg : Case := .lexical .erg

/-- The dative, a lexical Case. -/
@[match_pattern] abbrev Case.dat : Case := .lexical .dat

/-- The lexical accusative, which is not the structural accusative. -/
@[match_pattern] abbrev Case.lexAcc : Case := .lexical .acc

namespace Case

/-- The comparative value a Case is named for. Objective is an accusative: what Schebeck labels
accusative is labeled objective here (note 35), and the lexical accusative is one by name. -/
def label : Case → _root_.Case
  | .nom => .nom
  | .obj => .acc
  | .acc => .acc
  | .erg => .erg
  | .dat => .dat
  | .lexAcc => .acc

/-- The lexical Case a Case is, if it is one. -/
def lexical? : Case → Option Lexical
  | .lexical l => some l
  | _ => none

/-- The Case is assigned or checked by a functional head. -/
def IsFunctional (c : Case) : Prop := c = .nom ∨ c = .obj

variable {c : Case}

theorem IsFunctional.ne_acc (h : c.IsFunctional) : c ≠ .acc := by
  rcases h with rfl | rfl <;> decide

theorem IsFunctional.lexical_ne (h : c.IsFunctional) (l : Lexical) : lexical l ≠ c := by
  rcases h with rfl | rfl <;> exact nofun

end Case

/-- Where an argument sits at LF: the specifier of Agr-S, the specifier of Agr-O, or inside VP. -/
inductive Position where
  | specAgrS
  | specAgrO
  | inVP
  deriving DecidableEq, Repr

/-- The position of an argument with a Case of Nez Perce, as the tree (9) gives it. -/
def Case.position : Case → Position
  | .nom | .erg => .specAgrS
  | .obj => .specAgrO
  | .acc | .dat | .lexAcc => .inVP

variable {c e : Case} {args r : List (Option Lexical)} {d : List Case}

/-! ### The Max. Acc. formula -/

/-- The Max. Acc. formula (27) on a verb's arguments, each with the lexical Case it assigns. -/
def maxAcc (args : List (Option Lexical)) : ℤ := args.length - args.countP Option.isSome - 1

-- p. 205: one less than the number of arguments that need structural Case
theorem maxAcc_eq_count_sub_one (args : List (Option Lexical)) :
    maxAcc args = args.count none - 1 := by
  induction args with
  | nil => simp [maxAcc]
  | cons o r ih => cases o <;> grind [maxAcc]

theorem toNat_maxAcc (args : List (Option Lexical)) :
    (maxAcc args).toNat = args.count none - 1 := by
  rw [maxAcc_eq_count_sub_one]; omega

theorem maxAcc_neg_iff : maxAcc args < 0 ↔ none ∉ args := by
  rw [maxAcc_eq_count_sub_one, ← List.count_eq_zero]; omega

-- p. 206
theorem maxAcc_values :
    maxAcc [none] = 0 ∧ maxAcc [none, none] = 1 ∧ maxAcc [some .erg, none] = 0 ∧
      maxAcc [none, none, none] = 2 ∧ maxAcc [some .erg, none, none] = 1 ∧
      maxAcc [some .erg, some .dat, none] = 0 := by
  decide

-- note 30, and (18b)
theorem maxAcc_negative : maxAcc [some .dat] = -1 ∧ maxAcc [some .erg, some .dat] = -1 := by
  decide

/-! ### Derivations -/

/-- Case on arguments, the highest first: an argument keeps its lexical Case, the highest caseless
arguments take the Cases `cs` in turn, and the remaining ones accusative. -/
@[simp] def place : List Case → List (Option Lexical) → List Case
  | _, [] => []
  | cs, some l :: r => .lexical l :: place cs r
  | [], none :: r => .acc :: place [] r
  | c :: cs, none :: r => c :: place cs r

theorem place_map_some_append (cs : List Case) (ls : List Lexical) (r : List (Option Lexical)) :
    place cs (ls.map some ++ r) = ls.map Case.lexical ++ place cs r := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [ih]

@[simp] theorem length_place (cs : List Case) (args : List (Option Lexical)) :
    (place cs args).length = args.length := by
  fun_induction place cs args <;> simp [*]

theorem count_acc_place (cs : List Case) (h : .acc ∉ cs) (args : List (Option Lexical)) :
    (place cs args).count .acc = args.count none - cs.length := by
  fun_induction place cs args <;> grind

theorem count_acc_place_singleton (hc : c.IsFunctional) (args : List (Option Lexical)) :
    (place [c] args).count .acc = (maxAcc args).toNat := by
  rw [toNat_maxAcc, count_acc_place _ (by simpa using hc.ne_acc.symm)]; rfl

theorem count_place_le (he : e.IsFunctional) (cs : List Case) (args : List (Option Lexical)) :
    (place cs args).count e ≤ cs.count e := by
  have := he.ne_acc
  have := he.lexical_ne
  fun_induction place cs args <;> grind

/-! ### Economy -/

/-- The Cases an argument can bear: a lexical Case is kept, and a caseless argument takes accusative
inside VP or the Case `c` outside it. -/
def Slot (c : Case) : Option Lexical → Case → Prop
  | some l, d => d = .lexical l
  | none, d => d = .acc ∨ d = c

/-- A logically possible derivation with `c` the Case outside VP: the formula (27), with a floor at
zero, bounds the accusatives, and there is one position for `c`. -/
structure Candidate (c : Case) (args : List (Option Lexical)) (d : List Case) : Prop where
  slots : List.Forall₂ (Slot c) args d
  count_acc_le : d.count .acc ≤ (maxAcc args).toNat
  count_le_one : d.count c ≤ 1

/-- The path of the argument that moves out of VP for `c`, its depth among the arguments, and
nothing if no argument moves. -/
def pathLength (c : Case) (d : List Case) : ℕ := if c ∈ d then d.idxOf c else 0

theorem pathLength_of_mem (h : c ∈ d) : pathLength c d = d.idxOf c := by simp [pathLength, h]

theorem forall₂_slot_place_nil (c : Case) (args : List (Option Lexical)) :
    List.Forall₂ (Slot c) args (place [] args) := by
  induction args with
  | nil => simp
  | cons o r ih => cases o <;> simp [Slot, ih]

theorem forall₂_slot_place (c : Case) (args : List (Option Lexical)) :
    List.Forall₂ (Slot c) args (place [c] args) := by
  induction args with
  | nil => simp
  | cons o r ih => cases o <;> simp [Slot, ih, forall₂_slot_place_nil]

theorem count_acc_add_count (hc : c.IsFunctional) (h : List.Forall₂ (Slot c) args d) :
    d.count .acc + d.count c = args.count none := by
  induction h with
  | nil => simp
  | @cons o e r d he _ ih =>
    have := hc.ne_acc
    have := hc.lexical_ne
    cases o <;> grind [Slot]

theorem candidate_place (hc : c.IsFunctional) (args : List (Option Lexical)) :
    Candidate c args (place [c] args) where
  slots := forall₂_slot_place c args
  count_acc_le := (count_acc_place_singleton hc args).le
  count_le_one := by simpa using count_place_le hc [c] args

theorem Candidate.mem (hc : c.IsFunctional) (h : Candidate c args d) (ha : none ∈ args) :
    c ∈ d := by
  have hk := List.count_pos_iff.2 ha
  have hle := h.count_acc_le
  rw [toNat_maxAcc] at hle
  have := count_acc_add_count hc h.slots
  exact List.count_pos_iff.1 (by omega)

theorem eq_place_of_none_notMem (h : List.Forall₂ (Slot c) args d) (ha : none ∉ args)
    (cs : List Case) : d = place cs args := by
  induction h with
  | nil => simp
  | @cons o e r d he _ ih => cases o <;> grind [Slot, place]

theorem idxOf_place_le (hc : c.IsFunctional) (h : List.Forall₂ (Slot c) args d) :
    (place [c] args).idxOf c ≤ d.idxOf c := by
  induction h with
  | nil => simp
  | @cons o e r d he _ ih =>
    have := hc.lexical_ne
    cases o <;> grind [Slot, place]

theorem eq_place_nil_of_notMem (h : List.Forall₂ (Slot c) args d) (h0 : c ∉ d) :
    d = place [] args := by
  induction h with
  | nil => simp
  | @cons o e r d he _ ih => cases o <;> grind [Slot, place]

theorem eq_place_of_idxOf_le (hc : c.IsFunctional) (h : Candidate c args d)
    (hle : d.idxOf c ≤ (place [c] args).idxOf c) : d = place [c] args := by
  obtain ⟨hs, -, h1⟩ := h
  induction hs with
  | nil => simp
  | @cons o e r d he hs ih =>
    cases o with
    | some l =>
      obtain rfl : e = .lexical l := he
      have hne := hc.lexical_ne l
      simp only [place, List.idxOf_cons, beq_iff_eq, hne, reduceIte] at hle
      simp only [List.count_cons_of_ne hne] at h1
      simp [ih (by simpa using hle) h1]
    | none =>
      rcases (he : e = .acc ∨ e = c) with rfl | rfl
      · simp [hc.ne_acc.symm] at hle
      · simp only [List.count_cons_self] at h1
        simp [eq_place_nil_of_notMem hs (List.count_eq_zero.1 (by omega))]

-- p. 207
theorem minimalFor_pathLength_iff (hc : c.IsFunctional) :
    MinimalFor (Candidate c args) (pathLength c) d ↔ d = place [c] args := by
  by_cases ha : none ∈ args
  · have hm (d : List Case) (h : Candidate c args d) := pathLength_of_mem (h.mem hc ha)
    have hp := candidate_place hc args
    constructor
    · rintro ⟨hd, hmin⟩
      refine eq_place_of_idxOf_le hc hd ?_
      rw [← hm _ hd, ← hm _ hp]
      exact MinimalFor.le ⟨hd, hmin⟩ hp
    · rintro rfl
      refine ⟨hp, fun j hj _ ↦ ?_⟩
      rw [hm _ hp, hm _ hj]
      exact idxOf_place_le hc hj.slots
  · have hu (d : List Case) (h : Candidate c args d) := eq_place_of_none_notMem h.slots ha [c]
    constructor
    · exact fun h ↦ hu d h.1
    · rintro rfl
      exact ⟨candidate_place hc args, fun j hj _ ↦ by rw [hu j hj]⟩

/-! ### Assignment and the positions outside VP -/

/-- Whether a language's verbs assign a Case obligatorily, optionally, or not at all. -/
inductive Assignment where
  | obligatory
  | optional
  | lacking
  deriving DecidableEq, Repr, Fintype

variable {a : Assignment}

/-- The numbers of structural accusatives a verb assigns, `m` being the formula's maximum: as many
as it can as a rule, as in Nez Perce (p. 202), as many as it likes up to that, or none. -/
def Assignment.counts (m : ℕ) : Assignment → List ℕ
  | .obligatory => [m]
  | .optional => List.range (m + 1)
  | .lacking => [0]

theorem Assignment.le_of_mem_counts {m n : ℕ} (h : n ∈ a.counts m) : n ≤ m := by
  cases a <;> simp [counts] at h <;> omega

/-- The markings a verb's entry allows a slot with the lexical Case `l`, as in (53), (54), (59). -/
def Assignment.options (l : Lexical) : Assignment → List (Option Lexical)
  | .obligatory => [some l]
  | .optional => [none, some l]
  | .lacking => [none]

/-- The Case of the highest caseless argument: nominative under a caseless subject, and otherwise,
the external subject position being full, what the language gives a denied object, `c`, objective
in Nez Perce and nominative in Hindi (p. 200). -/
def highestCase (c : Case) : List (Option Lexical) → Case
  | none :: _ => .nom
  | _ => c

/-- The Cases outside VP open to the caseless arguments, highest first. -/
def outside (c : Case) (args : List (Option Lexical)) : List Case :=
  highestCase c args :: if args.head? = some none then [.obj] else []

theorem isFunctional_highestCase (hc : c.IsFunctional) (args : List (Option Lexical)) :
    (highestCase c args).IsFunctional := by
  rcases args with _ | ⟨_ | _, _⟩
  · exact hc
  · exact .inl rfl
  · exact hc

theorem acc_notMem_outside (hc : c.IsFunctional) (args : List (Option Lexical)) :
    .acc ∉ outside c args := by
  rcases args with _ | ⟨_ | _, _⟩ <;> simp [outside, highestCase, hc.ne_acc.symm]

theorem count_obj_outside_le_one (hc : c.IsFunctional) (args : List (Option Lexical)) :
    (outside c args).count .obj ≤ 1 := by
  rcases args with _ | ⟨_ | _, _⟩ <;> rcases hc with rfl | rfl <;> simp [outside, highestCase]

/-- The derivations a language allows on a verb's arguments: as many accusatives as its setting
gives, and the remaining caseless arguments in the positions outside VP, if there are enough. -/
def derivations (a : Assignment) (c : Case) (args : List (Option Lexical)) : List (List Case) :=
  ((a.counts (maxAcc args).toNat).filter (args.count none - · ≤ (outside c args).length)).map
    fun n ↦ place ((outside c args).take (args.count none - n)) args

theorem mem_derivations :
    d ∈ derivations a c args ↔ ∃ n ∈ a.counts (maxAcc args).toNat,
      args.count none - n ≤ (outside c args).length ∧
        place ((outside c args).take (args.count none - n)) args = d := by
  simp [derivations, and_assoc]

theorem exists_eq_place_of_mem_derivations (hd : d ∈ derivations a c args) (ha : none ∈ args) :
    ∃ cs, d = place (highestCase c args :: cs) args := by
  obtain ⟨n, hn, -, rfl⟩ := mem_derivations.1 hd
  have hle := Assignment.le_of_mem_counts hn
  rw [toNat_maxAcc] at hle
  have hk := List.count_pos_iff.2 ha
  obtain ⟨m, hm⟩ : ∃ m, args.count none - n = m + 1 := ⟨args.count none - n - 1, by omega⟩
  exact ⟨_, by rw [hm, outside, List.take_succ_cons]⟩

theorem derivations_obligatory (c : Case) (args : List (Option Lexical)) :
    derivations .obligatory c args = [place [highestCase c args] args] := by
  simp only [derivations, Assignment.counts, toNat_maxAcc, List.filter_cons, List.filter_nil]
  by_cases ha : none ∈ args
  · have hk := List.count_pos_iff.2 ha
    have h1 : args.count none - (args.count none - 1) = 1 := by omega
    simp [h1, outside]
  · have h0 : args.count none = 0 := List.count_eq_zero.2 ha
    simp [h0, eq_place_of_none_notMem (forall₂_slot_place_nil c args) ha [highestCase c args]]

/-- Under obligatory accusative a clause's one pattern is what the formula and economy select among
the logically possible derivations: the highest caseless argument is denied accusative and moves out
of VP by the shortest path. -/
theorem mem_derivations_obligatory_iff (hc : c.IsFunctional) :
    d ∈ derivations .obligatory c args ↔
      MinimalFor (Candidate (highestCase c args) args) (pathLength (highestCase c args)) d := by
  rw [derivations_obligatory, List.mem_singleton,
    minimalFor_pathLength_iff (isFunctional_highestCase hc args)]

/-! ### The generalizations -/

-- (27) as a ceiling, in every setting
theorem count_acc_le_of_mem_derivations (hc : c.IsFunctional) (hd : d ∈ derivations a c args) :
    d.count .acc ≤ (maxAcc args).toNat := by
  obtain ⟨n, hn, hle, rfl⟩ := mem_derivations.1 hd
  have hn' := Assignment.le_of_mem_counts hn
  rw [toNat_maxAcc] at hn' ⊢
  rw [count_acc_place _ (fun hm ↦ acc_notMem_outside hc args (List.mem_of_mem_take hm)),
    List.length_take]
  omega

-- p. 205, (26): under obligatory accusative the ceiling is reached
theorem count_acc_of_mem_derivations_obligatory (hc : c.IsFunctional)
    (hd : d ∈ derivations .obligatory c args) : d.count .acc = (maxAcc args).toNat := by
  rw [derivations_obligatory, List.mem_singleton] at hd
  exact hd ▸ count_acc_place_singleton (isFunctional_highestCase hc args) args

-- p. 187, and the abstract: one objective per clause
theorem count_obj_le_one_of_mem_derivations (hc : c.IsFunctional)
    (hd : d ∈ derivations a c args) : d.count .obj ≤ 1 := by
  obtain ⟨n, -, -, rfl⟩ := mem_derivations.1 hd
  have h := count_place_le (e := .obj) (.inr rfl)
    ((outside c args).take (args.count none - n)) args
  exact h.trans (((List.take_sublist _ _).count_le _).trans (count_obj_outside_le_one hc args))

-- without accusative the limit of one position has force
theorem derivations_lacking_three : derivations .lacking .obj [none, none, none] = [] := by
  decide

-- p. 206 (i)
theorem head?_ne_acc_of_mem_derivations {o : Option Lexical}
    (hd : d ∈ derivations a c (o :: r)) : d.head? ≠ some .acc := by
  cases o with
  | none =>
    obtain ⟨cs, rfl⟩ := exists_eq_place_of_mem_derivations hd (by simp)
    simp [highestCase]
  | some l =>
    obtain ⟨n, -, -, rfl⟩ := mem_derivations.1 hd
    simp

-- (19), read weakly
/-- In a clause with a lexically Cased subject the highest caseless object has no structural
accusative, whatever the language does with accusative. -/
theorem getElem?_ne_acc_of_mem_derivations (hc : c.IsFunctional) {l : Lexical} {ls : List Lexical}
    (hd : d ∈ derivations a c (some l :: (ls.map some ++ none :: r))) :
    d[ls.length + 1]? ≠ some .acc := by
  obtain ⟨cs, rfl⟩ := exists_eq_place_of_mem_derivations hd (by simp)
  simp [highestCase, place_map_some_append, hc.ne_acc]

-- (18)
theorem ergative_patterns :
    [.erg, .nom] ∈ derivations .obligatory .nom [some .erg, none] ∧
      [.erg, .dat] ∈ derivations .obligatory .obj [some .erg, some .dat] ∧
      [.erg, .obj] ∈ derivations .obligatory .obj [some .erg, none] := by
  decide

-- (18d), and the dative of (10b)
theorem lexical_acc_notMem (hc : c.IsFunctional) (l : Lexical) :
    [.lexical l, .acc] ∉ derivations a c [some l, none] := fun hd ↦ by
  simpa using getElem?_ne_acc_of_mem_derivations (ls := []) (r := []) hc hd

-- p. 204: the strong interpretation fails where (24b) succeeds
theorem strong_underivable :
    derivations .lacking .obj [some .erg, none, none] = [] ∧
      [.erg, .obj, .acc] ∈ derivations .obligatory .obj [some .erg, none, none] := by
  decide

-- p. 204: inherent accusative rescues the strong interpretation only to overgenerate; pp. 201, 203
theorem inherent_accusative_overgenerates :
    derivations .lacking .obj [some .erg, none, some .acc] = [[.erg, .obj, .lexAcc]] ∧
      derivations .lacking .obj [some .erg, some .acc] = [[.erg, .lexAcc]] ∧
      derivations .lacking .obj [some .erg, some .dat, some .acc] = [[.erg, .dat, .lexAcc]] ∧
      Case.lexAcc.label = .acc := by
  decide

-- p. 204, p. 207: on the weak reading of Burzio's generalization, with no inherent accusative
theorem double_object_passive : derivations .obligatory .nom [none, none] = [[.nom, .acc]] := by
  decide

-- p. 207: an external subject with a lexical object assigns no accusative
theorem burzio_too_strong : derivations .obligatory .obj [none, some .dat] = [[.nom, .dat]] := by
  decide

-- pp. 205-206: one argument, caseless or lexically Cased
theorem derivations_intransitive (a : Assignment) (c : Case) :
    derivations a c [none] = [[.nom]] := by
  cases a <;> rfl

theorem derivations_lexical_intransitive (a : Assignment) (c : Case) (l : Lexical) :
    derivations a c [some l] = [[.lexical l]] := by
  cases a <;> rfl

-- p. 202, note 26: nominative-objective without accusative, or beside nominative-accusative
theorem nom_obj_mem :
    [.nom, .obj] ∈ derivations .lacking .obj [none, none] ∧
      [.nom, .obj] ∈ derivations .optional .obj [none, none] ∧
      [.nom, .acc] ∈ derivations .optional .obj [none, none] := by
  decide

-- p. 223 is a slip
theorem nom_acc_notMem_lacking (c : Case) :
    [.nom, .acc] ∉ derivations .lacking c [none, none] := by
  show _ ∉ [[Case.nom, Case.obj]]
  decide

/-! ### Typological variation -/

/-- A language's settings: ergative on transitive subjects, dative on goals, its accusative, and
what a denied object takes. -/
structure Params where
  ergative : Assignment
  dative : Assignment
  accusative : Assignment := .obligatory
  deniedObject : Case := .obj
  deriving DecidableEq, Repr

namespace Params

variable (P : Params)

/-- The intransitive, transitive and ditransitive verbs the settings allow. -/
def frames : List (List (Option Lexical)) :=
  [none] :: (P.ergative.options .erg).map ([·, none]) ++
    (P.ergative.options .erg).flatMap fun s ↦ (P.dative.options .dat).map ([s, ·, none])

/-- The derivable Case patterns. -/
def patterns : List (List Case) := P.frames.flatMap (derivations P.accusative P.deniedObject)

/-- The Cases of subjects and objects a language shows, ignoring the dative. -/
def coreCases : Finset Case := P.patterns.flatten.toFinset.erase .dat

end Params

/-- Nez Perce assigns ergative and dative optionally. -/
def nezPerce : Params := { ergative := .optional, dative := .optional }

/-- Thangu assigns both obligatorily. -/
def thangu : Params := { ergative := .obligatory, dative := .obligatory }

/-- Kalkatungu assigns ergative obligatorily and dative optionally. -/
def kalkatungu : Params := { ergative := .obligatory, dative := .optional }

-- (60)
theorem nezPerce_patterns :
    nezPerce.patterns = [[.nom], [.nom, .acc], [.erg, .obj], [.nom, .acc, .acc],
      [.nom, .dat, .acc], [.erg, .obj, .acc], [.erg, .dat, .obj]] := by
  decide

theorem thangu_patterns : thangu.patterns = [[.nom], [.erg, .obj], [.erg, .dat, .obj]] := by
  decide

theorem kalkatungu_patterns :
    kalkatungu.patterns = [[.nom], [.erg, .obj], [.erg, .obj, .acc], [.erg, .dat, .obj]] := by
  decide

-- p. 223: there is no parameter of ergativity beyond the verbs' ability to assign the Case
theorem patterns_of_ergative_lacking :
    ({ ergative := .lacking, dative := .lacking } : Params).patterns =
      [[.nom], [.nom, .acc], [.nom, .acc, .acc]] := by
  decide

-- four-way, three-way, four-way
theorem card_coreCases :
    nezPerce.coreCases.card = 4 ∧ thangu.coreCases.card = 3 ∧ kalkatungu.coreCases.card = 4 := by
  decide

-- p. 216: accusative never surfaces in Thangu, whether or not its verbs can assign it
theorem thangu_accusative_irrelevant (a : Assignment) :
    ({ ergative := .obligatory, dative := .obligatory, accusative := a } : Params).patterns =
      thangu.patterns := by
  cases a <;> decide

-- (54), (60): the limit of one position outside VP excludes a ditransitive without dative
theorem dative_not_forced :
    ({ ergative := .obligatory, dative := .optional, accusative := .lacking } : Params).patterns =
      thangu.patterns := by
  decide

-- pp. 216, 221: lacking accusative does not force ergative, so a Case shortage cannot explain it
theorem case_shortage_fails :
    [.nom, .obj] ∈ ({ ergative := .optional, dative := .obligatory, accusative := .lacking } :
      Params).patterns := by
  decide

-- the fragment's paradigm has the comparative values of the four-way system: objective and
-- accusative are one comparative accusative
theorem image_label_coreCases :
    nezPerce.coreCases.image Case.label = Finset.univ.image NezPerce.Case.label := by
  decide

-- note 35: Thangu's only object Case is the accusative of Schebeck's description
theorem image_label_coreCases_thangu :
    thangu.coreCases.image Case.label = {.nom, .erg, .acc} := by
  decide

/-! ### The rows -/

/-- The Case names of the rows. -/
def caseTable : List (String × Case) :=
  [("nominative", .nom), ("objective", .obj), ("accusative", .acc), ("ergative", .erg),
    ("dative", .dat), ("lexical-accusative", .lexAcc)]

/-- A row's Cases, in the Agent Goal Theme order of (22). -/
def cases? (e : Datum) : Option (List Case) :=
  match e.features "case" with
  | [] => none
  | cs => cs.mapM (List.lookup · caseTable)

/-- A row of a language whose settings (60) gives, with those settings. -/
def patternRow? (e : Datum) : Option (List Case × Params) :=
  (cases? e).bind fun p ↦
    (e.byLanguage [(Glottocode.nezPerce, nezPerce), (Glottocode.dhangu, thangu),
      (Glottocode.kalkatungu, kalkatungu)]).map (p, ·)

-- (16), (22), and the clauses of sections 1 to 3
/-- The clauses and tables of Nez Perce, Thangu and Kalkatungu are derived exactly as far as they
are attested, from each language's settings for ergative and dative. -/
theorem rows_patterns :
    Datum.Checks patternRow? (fun r ↦ Judgment.Band.ofProp (r.1 ∈ r.2.patterns))
      Examples.all 45 := by
  decide

/-- A row of a language the paper compares, with what a denied object takes there. -/
def deniedRow? (e : Datum) : Option (List Case × Case) :=
  (cases? e).bind fun p ↦
    (e.byLanguage [(Glottocode.icelandic, Case.nom), (Glottocode.hindi, .nom),
      (Glottocode.faroese, .obj)]).map (p, ·)

-- (10) to (13), (63), notes 16 and 18: the verb's lexical Cases are read off the row itself
theorem rows_denied :
    Datum.Checks deniedRow?
      (fun r ↦ Judgment.Band.ofProp
        (r.1 ∈ derivations .obligatory r.2 (r.1.map Case.lexical?))) Examples.all 10 := by
  decide

/-! ### Agreement -/

/-- The portmanteau prefixes (48), by the person of the subject and the features of the objective
object. -/
def agreementPrefix : Person → Option (Person × Number) → List Morph
  | .third, some (.third, .singular) => [.pref "pée"]
  | .third, _ => [.pref "hi"]
  | _, some (.third, _) => [.pref "'e"]
  | _, _ => []

/-- The features of the argument in a position. -/
def phiAt (p : Position) (args : List (Case × Person × Number)) : Option (Person × Number) :=
  (args.find? fun a ↦ a.1.position = p).map (·.2)

/-- The prefix of a clause, which reads the arguments in the two agreement positions. -/
def agreement (args : List (Case × Person × Number)) : Option (List Morph) :=
  (phiAt .specAgrS args).map fun s ↦ agreementPrefix s.1 (phiAt .specAgrO args)

/-- The feature bundles of the rows. -/
def phiTable : List (String × Person × Number) :=
  [("1sg", .first, .singular), ("1pl", .first, .plural), ("2sg", .second, .singular),
    ("3sg", .third, .singular), ("3pl", .third, .plural)]

/-- A row's arguments with their Cases and features, and its prefix. -/
def agreementRow? (e : Datum) : Option (List (Case × Person × Number) × List Morph) :=
  (cases? e).bind fun cs ↦ ((e.features "phi").mapM (List.lookup · phiTable)).bind fun ps ↦
    (e.feature? "prefix").map fun x ↦ (cs.zip ps, if x = "Ø" then [] else [.pref x])

-- section 2: both subjects agree alike, and of the objects only the objective one
theorem rows_agreement :
    (∀ e ∈ Examples.all, ∀ r ∈ agreementRow? e, agreement r.1 = some r.2) ∧
      Datum.ReadCount agreementRow? Examples.all 23 := by
  decide

-- p. 212, (42): were the accusative to agree, the prefix would be pée
theorem accusative_would_agree :
    agreementPrefix .third (phiAt .inVP [(.nom, .third, .singular), (.acc, .third, .singular)]) =
      [.pref "pée"] := by
  decide

/-! ### Three levels of alignment -/

/-- The Case of the core roles, the transitive subject having the lexical Case `s`. -/
def marking (s : Option Lexical) : ArgumentRole → Option Case
  | .S => (place [highestCase .obj [none]] [none]).head?
  | .A => (place [highestCase .obj [s, none]] [s, none]).head?
  | .P => (place [highestCase .obj [s, none]] [s, none])[1]?
  | _ => none

/-- The exponent of a Case in a language, from the table (58). -/
def exponent (l : Glottocode) (c : Case) : Option String :=
  (Examples.all.find? fun e ↦ e.language = l ∧ e.parse? "cell" caseTable = some c).bind
    (·.feature? "exponent")

/-- A cell of the table (58): its Case, and the position its agreement column reports. -/
def tableRow? (e : Datum) : Option (Case × Position) :=
  (e.parse? "cell" caseTable).bind fun c ↦
    (e.parse? "agreement" [("subject", .specAgrS), ("object", .specAgrO), ("none", .inVP)]).map
      (c, ·)

-- (58): the agreement of a Case is its position
theorem rows_table_58 :
    (∀ e ∈ Examples.all, ∀ r ∈ tableRow? e, r.1.position = r.2) ∧
      Datum.ReadCount tableRow? Examples.all 8 := by
  decide

-- (58), p. 217
/-- One clause of Kalkatungu is ergative in its morphology, nominative-accusative in its agreement,
and tripartite in its abstract Cases, only the ergative being marked. -/
theorem kalkatungu_alignments :
    IsTripartite (marking (some .erg)) ∧
      IsErgative (fun r ↦ (marking (some .erg) r).bind (exponent .kalkatungu)) ∧
      IsAccusative (fun r ↦ (marking (some .erg) r).map Case.position) := by
  decide

-- p. 196: tripartite beside accusative in Case, accusative throughout in agreement
theorem nezPerce_alignments :
    IsTripartite (marking (some .erg)) ∧ IsAccusative (marking none) ∧
      IsTripartite (fun r ↦ (marking (some .erg) r).bind (exponent .nezPerce)) ∧
      IsNeutral (fun r ↦ (marking none r).bind (exponent .nezPerce)) ∧
      IsAccusative (fun r ↦ (marking (some .erg) r).map Case.position) ∧
      IsAccusative (fun r ↦ (marking none r).map Case.position) := by
  decide

-- p. 217: a four-way system whose structural Cases are unmarked looks two-way
theorem card_image_exponent :
    (kalkatungu.coreCases.image (exponent .kalkatungu)).card = 2 ∧
      (nezPerce.coreCases.image (exponent .nezPerce)).card = 3 := by
  decide

/-! ### Dependent case -/

/-- An argument's lexical Case as a comparative value, the input of the rules of dependent case. -/
def lexicalValue (o : Option Lexical) : Option _root_.Case := o.map fun l ↦ (Case.lexical l).label

/-- The value the accusative rules of dependent case give an argument bearing a Case, where they
give it one: the elsewhere case for nominative, the dependent accusative for accusative, and a
lexical Case itself. They have no objective. -/
def Case.dependentValue : Case → Option (_root_.Case × _root_.Case.Mechanism)
  | .nom => some (.nom, .unmarked)
  | .obj => none
  | .acc => some (.acc, .dependent)
  | .lexical l => some ((Case.lexical l).label, .lexical)

theorem getElem?_place (cs : List Case) (args : List (Option Lexical)) (i : ℕ) :
    (place cs args)[i]? = args[i]?.map
      (Option.elim · (cs.getD ((args.take i).count none) .acc) Case.lexical) := by
  fun_induction place cs args generalizing i <;> cases i <;> simp_all

theorem map_value?_assign_eq_map_place (args : List (Option Lexical)) :
    ((Rules.ofAlignment .accusative).assign lexicalValue args).map (·.2.value?) =
      (place [.nom] args).map Case.dependentValue := by
  refine List.ext_getElem? fun i ↦ ?_
  simp only [List.getElem?_map, getElem?_place]
  rcases hi : args[i]? with _ | _ | l
  · simp [List.getElem?_eq_none_iff.1 hi]
  · by_cases h : none ∈ args.take i
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (List.count_pos_iff.2 h).ne'
      rw [Rules.assign_getElem?_low _ hi rfl h rfl rfl rfl]
      simp [hk, Case.dependentValue]
    · rw [Rules.assign_getElem?_unmarked _ hi rfl (c := .nom) (fun y hy hly ↦ h (by
        simpa [show y = none by simpa [lexicalValue] using hly] using hy)) rfl rfl]
      simp [List.count_eq_zero.2 h, Case.dependentValue]
  · rw [Rules.assign_getElem?_of_some _ hi (c := (Case.lexical l).label) rfl]
    rfl

-- (10), (12), (13)
/-- Where objects can be nominative, the accusative rule of dependent case, with these lexical Cases
as its input, derives every pattern argument by argument. -/
theorem map_value?_assign (hd : d ∈ derivations .obligatory .nom args) :
    ((Rules.ofAlignment .accusative).assign lexicalValue args).map (·.2.value?) =
      d.map Case.dependentValue := by
  rw [derivations_obligatory, List.mem_singleton] at hd
  have : highestCase .nom args = .nom := by rcases args with _ | ⟨_ | _, _⟩ <;> rfl
  rw [hd, this, map_value?_assign_eq_map_place]

-- p. 208 calls the formula descriptive; the ergative rules too mark all arguments but one, so the
-- theorem above, which says which, is the stronger
theorem countP_dependent_assign (args : List (Option Lexical)) :
    ((Rules.ofAlignment .accusative).assign lexicalValue args).countP
        (fun p ↦ p.2.value?.map Prod.snd = some .dependent) = (maxAcc args).toNat := by
  have hm := congrArg (List.countP fun v ↦ v.map Prod.snd = some _root_.Case.Mechanism.dependent)
    (map_value?_assign_eq_map_place args)
  simp only [List.countP_map, Function.comp_def] at hm
  rw [hm, ← count_acc_place_singleton (c := .nom) (.inl rfl), List.count]
  refine List.countP_congr fun d _ ↦ ?_
  rcases d with _ | _ | _ | _ <;> simp [Case.dependentValue]

-- (5), (58): the rules give the object of an ergative subject the elsewhere case of a subject, but
-- objective is overt and agrees as an object
theorem objective_not_elsewhere :
    ((Rules.ofAlignment .accusative).assign lexicalValue [some .erg, none]).map (·.2.value?) =
        [some (.erg, .lexical), some (.nom, .unmarked)] ∧
      exponent .nezPerce .obj ≠ exponent .nezPerce .nom ∧
      Case.obj.position ≠ Case.nom.position := by
  decide

end Woolford1997
