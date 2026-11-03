module

public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Woolford1997
public import Linglib.Fragments.NezPerce.Case
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Minimalist.Case.Dependent
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic

/-!
# Woolford (1997): Four-Way Case Systems: Ergative, Nominative, Objective and Accusative

This file derives the Case patterns of Nez Perce, Thangu and Kalkatungu from an inventory in which
ergative is lexical and objects have two structural Cases, objective outside VP and accusative
inside it. The formula $\#\text{arguments} - \#\text{lexical Cases} - 1$ bounds the accusatives and
[economy picks the argument that moves out of VP](##mem_derivations_obligatory_iff), so [a lexically
Cased subject denies accusative to its highest object](##getElem?_ne_acc_of_mem_derivations).
Settings for ergative and dative [give each language its patterns](##rows_patterns), and one
Kalkatungu clause is
[ergative in morphology, accusative in agreement and tripartite in Case](##kalkatungu_alignments).
The accusative rule of dependent case [derives the same patterns](##map_value?_assign) where objects
can be nominative.

## Implementation notes

* P. 207 states economy for one denied argument, and so does this file. Where two arguments leave
  VP, as without accusative, `place` gives the higher one the higher position by definition.
* The comparison with dependent case is not the paper's. It feeds the accusative rules the paper's
  lexical ergative, where Marantz's is dependent, and [fails for
  objective](##objective_not_elsewhere).

## Errata

* P. 223 says nominative-accusative where p. 202 has nominative-objective: [the former cannot arise
  without accusative](##nom_acc_notMem_lacking).
* P. 207 promises evidence in section 3 that languages can lack accusative, but [Thangu's patterns
  do not depend on it](##thangu_accusative_irrelevant) and Kalkatungu has it.
* Note 30's negative case is [any verb with only lexical Cases](##maxAcc_neg_iff), as in (18b) and
  (63), not just intransitives.
* (8) has the surface form of the starred (22B.7): its dative and objective are both *-na*.
* Thangu's obligatory dative in (60) [is not forced](##dative_not_forced).

## TODO

* The passives (14), (15) and the claim of section 1.2.1 about them.
* The number agreement of (28) to (34).
* Accusative Case Blocking (p. 208).

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

/-- The Max. Acc. formula (27) on a verb's arguments, highest first, each with the lexical Case it
assigns. The prose before (27) also subtracts Case from a preposition, which no example tests. -/
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

/-- Case on arguments, the highest first: an argument keeps its lexical Case, the functional heads
of (1a) value the highest caseless arguments with `cs` in turn, and V gives the rest accusative. -/
def place (cs : List Case) (args : List (Option Lexical)) : List Case :=
  (Minimalist.agreeValues (fun _ ↦ True) cs
    (_root_.Case.Valuation.initial (fun o ↦ _root_.Case.Valuation.offer (o.map .lexical)) args)).map
      fun p ↦ p.2.value?.getD .acc

@[simp] theorem place_nil_right (cs : List Case) : place cs [] = [] := by
  simp [place, _root_.Case.Valuation.initial]

@[simp] theorem place_some_cons (cs : List Case) (l : Lexical) (r : List (Option Lexical)) :
    place cs (some l :: r) = .lexical l :: place cs r := by
  simp [place, _root_.Case.Valuation.initial, Minimalist.agreeValues_cons_right_of_not]

@[simp] theorem place_nil_none_cons (r : List (Option Lexical)) :
    place [] (none :: r) = .acc :: place [] r := by
  simp [place, _root_.Case.Valuation.initial]

@[simp] theorem place_cons_none_cons (c : Case) (cs : List Case) (r : List (Option Lexical)) :
    place (c :: cs) (none :: r) = c :: place cs r := by
  simp [place, _root_.Case.Valuation.initial, Minimalist.agreeValues_cons_cons]

theorem place_map_some_append (cs : List Case) (ls : List Lexical) (r : List (Option Lexical)) :
    place cs (ls.map some ++ r) = ls.map Case.lexical ++ place cs r := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [ih]

theorem place_congr_of_none_notMem (cs cs' : List Case) (h : none ∉ args) :
    place cs args = place cs' args := by
  induction args with
  | nil => simp
  | cons o r ih =>
    cases o with
    | none => simp at h
    | some l => simp [ih fun hr ↦ h (List.mem_cons_of_mem _ hr)]

theorem getElem?_place (cs : List Case) (args : List (Option Lexical)) (i : ℕ) :
    (place cs args)[i]? = args[i]?.map
      (Option.elim · (cs.getD ((args.take i).count none) .acc) Case.lexical) := by
  induction args generalizing cs i with
  | nil => simp
  | cons o r ih => cases o <;> cases cs <;> cases i <;> simp_all

theorem count_acc_place (cs : List Case) (h : .acc ∉ cs) (args : List (Option Lexical)) :
    (place cs args).count .acc = args.count none - cs.length := by
  induction args generalizing cs with
  | nil => simp
  | cons o r ih =>
    cases o with
    | some l => simp [ih cs h]
    | none =>
      cases cs with
      | nil => simpa [List.count_cons] using ih [] h
      | cons c cs =>
        have hc : c ≠ .acc := fun hc ↦ h (hc ▸ List.mem_cons_self)
        simp [hc, ih cs fun hm ↦ h (List.mem_cons_of_mem _ hm)]

theorem count_acc_place_singleton (hc : c.IsFunctional) (args : List (Option Lexical)) :
    (place [c] args).count .acc = (maxAcc args).toNat := by
  rw [toNat_maxAcc, count_acc_place _ (by simpa using hc.ne_acc.symm)]; rfl

theorem count_place_le (he : e.IsFunctional) (cs : List Case) (args : List (Option Lexical)) :
    (place cs args).count e ≤ cs.count e := by
  induction args generalizing cs with
  | nil => simp
  | cons o r ih =>
    cases o with
    | some l => simpa [List.count_cons, he.lexical_ne l] using ih cs
    | none =>
      cases cs with
      | nil => simpa [List.count_cons, he.ne_acc.symm] using ih []
      | cons c cs =>
        simp only [place_cons_none_cons, List.count_cons]
        have := ih cs
        omega

/-! ### Economy -/

/-- The derivation in which the argument at `i` is denied accusative and takes `c` outside VP: the
derivations of p. 207 differ only in `i`, the length of that argument's path. -/
def denyAt (c : Case) (args : List (Option Lexical)) (i : ℕ) : List Case :=
  args.mapIdx fun j o ↦ o.elim (if j = i then c else .acc) Case.lexical

theorem idxOf_none_le {j : ℕ} (h : args[j]? = some none) : args.idxOf none ≤ j := by
  induction args generalizing j with
  | nil => simp at h
  | cons o r ih => cases o <;> cases j <;> simp_all

theorem count_take_eq_zero_iff {j : ℕ} (ha : none ∈ args) :
    (args.take j).count none = 0 ↔ j ≤ args.idxOf none := by
  induction args generalizing j with
  | nil => simp at ha
  | cons o r ih => cases o <;> cases j <;> simp_all

theorem denyAt_idxOf (c : Case) (args : List (Option Lexical)) :
    denyAt c args (args.idxOf none) = place [c] args := by
  refine List.ext_getElem? fun j ↦ ?_
  rw [denyAt, List.getElem?_mapIdx, getElem?_place]
  rcases hj : args[j]? with _ | _ | l
  · rfl
  · have ha := List.mem_of_getElem? hj
    by_cases h : j = args.idxOf none
    · simp [h, (count_take_eq_zero_iff ha).2 le_rfl]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (mt (count_take_eq_zero_iff ha).1
        (not_le.2 (lt_of_le_of_ne (idxOf_none_le hj) (Ne.symm h))))
      simp [h, hk]
  · rfl

-- p. 207: the shortest path is the highest caseless argument's
theorem minimalFor_iff {i : ℕ} :
    MinimalFor (fun i ↦ args[i]? = some none) id i ↔ none ∈ args ∧ i = args.idxOf none := by
  constructor
  · rintro ⟨hi, hmin⟩
    have ha : none ∈ args := List.mem_of_getElem? hi
    have hidx : args[args.idxOf none]? = some none := by
      simp [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 ha)]
    exact ⟨ha, (hmin hidx (idxOf_none_le hi)).antisymm (idxOf_none_le hi)⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨by simp [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 ha)],
      fun _ hj _ ↦ idxOf_none_le hj⟩

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

/-- The one pattern of a clause under obligatory accusative. -/
def pattern (c : Case) (args : List (Option Lexical)) : List Case :=
  place [highestCase c args] args

theorem derivations_obligatory (c : Case) (args : List (Option Lexical)) :
    derivations .obligatory c args = [pattern c args] := by
  simp only [derivations, Assignment.counts, toNat_maxAcc, List.filter_cons, List.filter_nil]
  by_cases ha : none ∈ args
  · have hk := List.count_pos_iff.2 ha
    have h1 : args.count none - (args.count none - 1) = 1 := by omega
    simp [h1, outside, pattern]
  · have h0 : args.count none = 0 := List.count_eq_zero.2 ha
    simp [h0, pattern, place_congr_of_none_notMem [] [highestCase c args] ha]

/-- Under obligatory accusative a clause's pattern is the logically possible derivation with the
shortest path out of VP, the formula having fixed how many arguments are denied accusative. -/
theorem mem_derivations_obligatory_iff (ha : none ∈ args) :
    d ∈ derivations .obligatory c args ↔
      ∃ i, MinimalFor (fun i ↦ args[i]? = some none) id i ∧
        d = denyAt (highestCase c args) args i := by
  rw [derivations_obligatory, List.mem_singleton, pattern, ← denyAt_idxOf]
  constructor
  · rintro rfl
    exact ⟨_, minimalFor_iff.2 ⟨ha, rfl⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rw [(minimalFor_iff.1 hi).2]

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

-- (25c): denying the lower object meets the formula, and economy alone excludes it
theorem economy_excludes :
    denyAt .obj [some .erg, none, none] 2 = [.erg, .acc, .obj] ∧
      ([.erg, .acc, .obj] : List Case).count .acc = (maxAcc [some .erg, none, none]).toNat ∧
      ¬ MinimalFor (fun i ↦ ([some .erg, none, none] : List (Option Lexical))[i]? = some none) id
        2 := by
  refine ⟨rfl, by decide, fun h ↦ ?_⟩
  simpa using (minimalFor_iff.1 h).2

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

-- p. 204: the strong interpretation, `.lacking` under a lexical subject, fails where (24b)
-- succeeds, and inherent accusative rescues it only to overgenerate (pp. 201, 203)
theorem strong_interpretation :
    derivations .lacking .obj [some .erg, none, none] = [] ∧
      [.erg, .obj, .acc] ∈ derivations .obligatory .obj [some .erg, none, none] ∧
      derivations .lacking .obj [some .erg, none, some .acc] = [[.erg, .obj, .lexAcc]] ∧
      derivations .lacking .obj [some .erg, some .acc] = [[.erg, .lexAcc]] ∧
      derivations .lacking .obj [some .erg, some .dat, some .acc] = [[.erg, .dat, .lexAcc]] ∧
      Case.lexAcc.label = .acc := by
  decide

-- pp. 204, 207: a double-object passive with no inherent accusative, and an external subject over a
-- lexical object with no accusative at all, so the formula is not Burzio's generalization
theorem burzio_patterns :
    derivations .obligatory .nom [none, none] = [[.nom, .acc]] ∧
      derivations .obligatory .obj [none, some .dat] = [[.nom, .dat]] := by
  decide

-- pp. 205-206: one argument, caseless or lexically Cased
theorem derivations_intransitive (a : Assignment) (c : Case) (l : Lexical) :
    derivations a c [none] = [[.nom]] ∧ derivations a c [some l] = [[.lexical l]] := by
  cases a <;> exact ⟨rfl, rfl⟩

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
what a denied object takes, one Case per language, so Hindi's objective *-ko* (notes 17, 43) is
left out. -/
structure Params where
  ergative : Assignment
  dative : Assignment
  accusative : Assignment := .obligatory
  deniedObject : Case := .obj
  deriving DecidableEq, Repr

namespace Params

variable (P : Params)

/-- The intransitive, transitive and ditransitive verbs the settings allow, intransitive subjects
being caseless as in the classic ergative type (p. 190). -/
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

-- (60), and p. 223: there is no parameter of ergativity beyond the verbs' ability to assign it
theorem patterns_table :
    nezPerce.patterns = [[.nom], [.nom, .acc], [.erg, .obj], [.nom, .acc, .acc],
      [.nom, .dat, .acc], [.erg, .obj, .acc], [.erg, .dat, .obj]] ∧
      thangu.patterns = [[.nom], [.erg, .obj], [.erg, .dat, .obj]] ∧
      kalkatungu.patterns = [[.nom], [.erg, .obj], [.erg, .obj, .acc], [.erg, .dat, .obj]] ∧
      ({ ergative := .lacking, dative := .lacking } : Params).patterns =
        [[.nom], [.nom, .acc], [.nom, .acc, .acc]] := by
  decide

-- four-way, three-way, four-way; objective and accusative are one comparative accusative, as in the
-- fragment's paradigm, and Thangu's only object Case is Schebeck's accusative (note 35)
theorem coreCases_table :
    nezPerce.coreCases.card = 4 ∧ thangu.coreCases.card = 3 ∧ kalkatungu.coreCases.card = 4 ∧
      nezPerce.coreCases.image Case.label = Finset.univ.image NezPerce.Case.label ∧
      thangu.coreCases.image Case.label = {.nom, .erg, .acc} := by
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

/-- The Case of each role where a denied object is objective, the subject having the lexical Case
`s` and the goal the lexical Case `g`. -/
def marking (s g : Option Lexical) : ArgumentRole → Option Case
  | .S => (pattern .obj [none]).head?
  | .A => (pattern .obj [s, none]).head?
  | .P => (pattern .obj [s, none])[1]?
  | .R => (pattern .obj [s, g, none])[1]?
  | .T => (pattern .obj [s, g, none])[2]?

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
    IsTripartite (marking (some .erg) none) ∧
      IsErgative (fun r ↦ (marking (some .erg) none r).bind (exponent .kalkatungu)) ∧
      IsAccusative (fun r ↦ (marking (some .erg) none r).map Case.position) := by
  decide

-- p. 196: tripartite beside accusative in Case, accusative throughout in agreement
theorem nezPerce_alignments :
    IsTripartite (marking (some .erg) none) ∧ IsAccusative (marking none none) ∧
      IsTripartite (fun r ↦ (marking (some .erg) none r).bind (exponent .nezPerce)) ∧
      IsNeutral (fun r ↦ (marking none none r).bind (exponent .nezPerce)) ∧
      IsAccusative (fun r ↦ (marking (some .erg) none r).map Case.position) ∧
      IsAccusative (fun r ↦ (marking none none r).map Case.position) := by
  decide

-- (7), (8), p. 187: objective goes to the goal, and with a dative goal to the theme, "as if the
-- goal were not present"; without an ergative the objects are all accusative
theorem ditransitive_alignments :
    IsSecundative (marking (some .erg) none) ∧ IsIndirective (marking (some .erg) (some .dat)) ∧
      IsIndirective (marking none (some .dat)) ∧
      ¬ IsSecundative (marking none none) ∧ ¬ IsIndirective (marking none none) := by
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
  rw [hd, pattern, this, map_value?_assign_eq_map_place]

-- p. 208 calls the formula descriptive
theorem countP_dependent_assign (args : List (Option Lexical)) :
    ((Rules.ofAlignment .accusative).assign lexicalValue args).countP
        (fun p ↦ p.2.value?.map Prod.snd = some .dependent) = (maxAcc args).toNat := by
  have hm := congrArg (List.countP fun v ↦ v.map Prod.snd = some _root_.Case.Mechanism.dependent)
    (map_value?_assign_eq_map_place args)
  simp only [List.countP_map, Function.comp_def] at hm
  rw [hm, ← count_acc_place_singleton (c := .nom) (.inl rfl), List.count]
  refine List.countP_congr fun d _ ↦ ?_
  rcases d with _ | _ | _ | _ <;> simp [Case.dependentValue]

-- the count alone does not single out the accusative rule: the ergative rule marks as many
-- arguments, though not the same ones, so the theorem that says which is the stronger
theorem ergative_rule_same_count :
    ((Rules.ofAlignment .ergative).assign lexicalValue [none, none, none]).map (·.2.value?) =
        [some (.erg, .dependent), some (.erg, .dependent), some (.abs, .unmarked)] ∧
      (maxAcc [none, none, none]).toNat = 2 := by
  decide

-- (5), (58): the rules give the object of an ergative subject the elsewhere case of a subject, but
-- objective is overt and agrees as an object
theorem objective_not_elsewhere :
    ((Rules.ofAlignment .accusative).assign lexicalValue [some .erg, none]).map (·.2.value?) =
        [some (.erg, .lexical), some (.nom, .unmarked)] ∧
      exponent .nezPerce .obj ≠ exponent .nezPerce .nom ∧
      Case.obj.position ≠ Case.nom.position := by
  decide

end Woolford1997
