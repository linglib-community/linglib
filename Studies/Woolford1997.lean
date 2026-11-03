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
ergative is lexical and objects have two structural Cases, objective outside VP and accusative
inside it. The formula $\#\text{arguments} - \#\text{lexical Cases} - 1$ bounds the accusatives and
[economy picks the arguments that move out of VP](##mem_derivations_iff), so [a lexically Cased
subject denies accusative to its highest object](##getElem?_ne_acc_of_mem_derivations). Settings for
ergative and dative [give each language its patterns](##rows_patterns), and one Kalkatungu clause is
[ergative in morphology, accusative in agreement and tripartite in Case](##kalkatungu_alignments).
The accusative rule of dependent case [derives the same patterns](##map_value?_assign) where objects
can be nominative.

## Implementation notes

* P. 207 states economy for one denied argument. Where two move, each path is compared separately
  and the higher argument takes the higher position.
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

instance : DecidablePred IsFunctional := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

variable {c : Case}

@[simp] theorem not_isFunctional_acc : ¬ acc.IsFunctional := by decide

@[simp] theorem not_isFunctional_lexical (l : Lexical) : ¬ (lexical l).IsFunctional := by
  simp [IsFunctional]

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

theorem place_congr_of_none_notMem (cs cs' : List Case) (h : none ∉ args) :
    place cs args = place cs' args := by
  induction args with
  | nil => simp
  | cons o r ih =>
    cases o with
    | none => simp at h
    | some l => simp [ih fun hr ↦ h (List.mem_cons_of_mem _ hr)]

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

/-- The Cases an argument can bear: a lexical Case is kept, and a caseless argument takes a
structural Case, accusative inside VP or a functional Case outside it. -/
def Slot : Option Lexical → Case → Prop
  | some l, d => d = .lexical l
  | none, d => d = .acc ∨ d.IsFunctional

/-- A logically possible derivation with `n` accusatives, `cs` being the Cases outside VP from the
highest position down: the positions fill from the top, each takes one argument, and the higher
argument takes the higher position. -/
structure Candidate (cs : List Case) (n : ℕ) (args : List (Option Lexical)) (d : List Case) :
    Prop where
  slots : List.Forall₂ Slot args d
  count_acc : d.count .acc = n
  filter_prefix : d.filter (·.IsFunctional) <+: cs

/-- The path of the argument that moves out of VP for a Case, its depth among the arguments, and
nothing if no argument moves for that Case. -/
def pathLength (d : List Case) (e : Case) : ℕ :=
  if e ∈ d.filter (·.IsFunctional) then d.idxOf e else 0

section

variable {cs : List Case} {n : ℕ}

theorem forall₂_slot_place (hcs : ∀ c ∈ cs, c.IsFunctional) (args : List (Option Lexical)) :
    List.Forall₂ Slot args (place cs args) := by
  induction args generalizing cs with
  | nil => simp
  | cons o r ih =>
    cases o with
    | some l => simpa [Slot] using ih hcs
    | none =>
      cases cs with
      | nil => simpa [Slot] using ih hcs
      | cons c cs =>
        simpa [Slot, hcs c List.mem_cons_self] using ih fun _ h ↦ hcs _ (List.mem_cons_of_mem _ h)

theorem filter_place (hcs : ∀ c ∈ cs, c.IsFunctional) (hk : cs.length ≤ args.count none) :
    (place cs args).filter (·.IsFunctional) = cs := by
  induction args generalizing cs with
  | nil => simpa [eq_comm] using hk
  | cons o r ih =>
    cases o with
    | some l => simpa using ih hcs (by simpa using hk)
    | none =>
      cases cs with
      | nil => simpa using ih hcs (by simp)
      | cons c cs =>
        simp only [place, List.filter_cons, hcs c List.mem_cons_self, decide_true, reduceIte]
        rw [ih (fun _ h ↦ hcs _ (List.mem_cons_of_mem _ h)) (by simpa using hk)]

theorem count_acc_add_length_filter (h : List.Forall₂ Slot args d) :
    d.count .acc + (d.filter (·.IsFunctional)).length = args.count none := by
  induction h with
  | nil => simp
  | @cons o e r d he _ ih =>
    cases o with
    | some l =>
      obtain rfl : e = .lexical l := he
      simpa using ih
    | none =>
      rcases (he : e = .acc ∨ e.IsFunctional) with rfl | hf
      · simp; omega
      · simp [hf, hf.ne_acc]; omega

theorem idxOf_place_le_idxOf_place_cons {cs : List Case} (hnd : (c :: cs).Nodup) (he : e ∈ cs)
    (r : List (Option Lexical)) : (place cs r).idxOf e ≤ (place (c :: cs) r).idxOf e := by
  induction r generalizing c cs with
  | nil => simp
  | cons o r ih =>
    cases o with
    | some l => by_cases h : Case.lexical l = e <;> simp [h, ih hnd he]
    | none =>
      cases cs with
      | nil => simp at he
      | cons c' cs =>
        by_cases h : c' = e
        · simp [h]
        · have hne : c ≠ e := by grind
          simpa [List.idxOf_cons, h, hne] using
            ih (List.nodup_cons.1 hnd).2 ((List.mem_cons.1 he).resolve_left (Ne.symm h))

theorem idxOf_place_le (h : List.Forall₂ Slot args d) (hnd : cs.Nodup)
    (hf : d.filter (·.IsFunctional) = cs) (he : e ∈ cs) :
    (place cs args).idxOf e ≤ d.idxOf e := by
  have hfun : e.IsFunctional := by subst hf; simpa using (List.mem_filter.1 he).2
  induction h generalizing cs with
  | nil => simp_all
  | @cons o e' r d he' hs ih =>
    cases o with
    | some l =>
      obtain rfl : e' = .lexical l := he'
      simpa [List.idxOf_cons, hfun.lexical_ne l] using
        ih hnd (by simpa using hf) he
    | none =>
      rcases (he' : e' = .acc ∨ e'.IsFunctional) with rfl | hm
      · have hf' : d.filter (·.IsFunctional) = cs := by simpa using hf
        cases cs with
        | nil => simp at he
        | cons c cs =>
          by_cases hc : c = e
          · simp [hc]
          · have h1 := idxOf_place_le_idxOf_place_cons hnd
              ((List.mem_cons.1 he).resolve_left (Ne.symm hc)) r
            simpa [List.idxOf_cons, hfun.ne_acc.symm, hc] using h1.trans (ih hnd hf' he)
      · obtain rfl : e' :: d.filter (·.IsFunctional) = cs := by simpa [hm] using hf
        by_cases hc : e' = e
        · simp [hc]
        · simpa [List.idxOf_cons, hc] using
            ih (List.nodup_cons.1 hnd).2 rfl ((List.mem_cons.1 he).resolve_left (Ne.symm hc))

theorem eq_place_of_forall_idxOf_le (h : List.Forall₂ Slot args d)
    (hf : d.filter (·.IsFunctional) = cs) (hnd : cs.Nodup)
    (hle : ∀ e ∈ cs, d.idxOf e ≤ (place cs args).idxOf e) : d = place cs args := by
  have hfun : ∀ {e : Case}, e ∈ cs → e.IsFunctional := fun he ↦ by
    subst hf; simpa using (List.mem_filter.1 he).2
  induction h generalizing cs with
  | nil => simp
  | @cons o e' r d he' hs ih =>
    cases o with
    | some l =>
      obtain rfl : e' = .lexical l := he'
      have := ih (by simpa using hf) hnd
        (fun e he ↦ by simpa [List.idxOf_cons, (hfun he).lexical_ne l] using hle e he) hfun
      simp [this]
    | none =>
      rcases (he' : e' = .acc ∨ e'.IsFunctional) with rfl | hm
      · have hf' : d.filter (·.IsFunctional) = cs := by simpa using hf
        cases cs with
        | nil => simp [ih hf' hnd (by simp) (by simp)]
        | cons c cs =>
          simpa [List.idxOf_cons, (hfun List.mem_cons_self).ne_acc.symm] using
            hle c List.mem_cons_self
      · obtain rfl : e' :: d.filter (·.IsFunctional) = cs := by simpa [hm] using hf
        have hne (e : Case) (he : e ∈ d.filter (·.IsFunctional)) : e' ≠ e :=
          fun h ↦ (List.nodup_cons.1 hnd).1 (h ▸ he)
        have := ih rfl (List.nodup_cons.1 hnd).2
          (fun e he ↦ by simpa [List.idxOf_cons, hne e he] using hle e (List.mem_cons_of_mem _ he))
          (fun he ↦ hfun (List.mem_cons_of_mem _ he))
        exact congrArg (e' :: ·) this

theorem Candidate.filter_eq {X : List Case} (h : Candidate X n args d) :
    d.filter (·.IsFunctional) = X.take (args.count none - n) := by
  have hc := count_acc_add_length_filter h.slots
  rw [h.count_acc] at hc
  have hp := List.prefix_iff_eq_take.1 h.filter_prefix
  rwa [show (d.filter (·.IsFunctional)).length = args.count none - n by omega] at hp

theorem Candidate.sub_le_length {X : List Case} (h : Candidate X n args d) :
    args.count none - n ≤ X.length := by
  have hc := count_acc_add_length_filter h.slots
  have := h.filter_prefix.length_le
  rw [h.count_acc] at hc
  omega

theorem candidate_place {X : List Case} (hX : ∀ c ∈ X, c.IsFunctional) (hn : n ≤ args.count none)
    (hk : args.count none - n ≤ X.length) :
    Candidate X n args (place (X.take (args.count none - n)) args) := by
  have hlen : (X.take (args.count none - n)).length = args.count none - n := by
    simp [List.length_take, hk]
  have hsub : ∀ c ∈ X.take (args.count none - n), c.IsFunctional :=
    fun c hc ↦ hX c (List.mem_of_mem_take hc)
  refine ⟨forall₂_slot_place hsub args, ?_, ?_⟩
  · rw [count_acc_place _ fun h ↦ (hsub _ h).ne_acc rfl, hlen]
    omega
  · rw [filter_place hsub (by omega)]
    exact List.take_prefix _ _

-- p. 207
theorem minimalFor_pathLength_iff {X : List Case} (hX : ∀ c ∈ X, c.IsFunctional) (hnd : X.Nodup)
    (hn : n ≤ args.count none) :
    MinimalFor (Candidate X n args) pathLength d ↔
      args.count none - n ≤ X.length ∧ d = place (X.take (args.count none - n)) args := by
  have hndt := hnd.sublist (List.take_sublist (args.count none - n) X)
  have hleast {j : List Case} (hj : Candidate X n args j) (hk : args.count none - n ≤ X.length) :
      pathLength (place (X.take (args.count none - n)) args) ≤ pathLength j := fun e ↦ by
    simp only [pathLength, (candidate_place hX hn hk).filter_eq, hj.filter_eq]
    split_ifs with he
    · exact idxOf_place_le hj.slots hndt hj.filter_eq he
    · exact le_rfl
  constructor
  · rintro ⟨hd, hmin⟩
    have hk := hd.sub_le_length
    have hp := candidate_place hX hn hk
    refine ⟨hk, eq_place_of_forall_idxOf_le hd.slots hd.filter_eq hndt fun e he ↦ ?_⟩
    have h := hmin hp (hleast hd hk) e
    simpa only [pathLength, hd.filter_eq, hp.filter_eq, he, reduceIte] using h
  · rintro ⟨hk, rfl⟩
    exact ⟨candidate_place hX hn hk, fun j hj _ ↦ hleast hj hk⟩

end

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

theorem isFunctional_of_mem_outside (hc : c.IsFunctional) (args : List (Option Lexical)) :
    ∀ e ∈ outside c args, e.IsFunctional := by
  rcases args with _ | ⟨_ | _, _⟩ <;> simp [outside, highestCase, Case.IsFunctional] <;> exact hc

theorem nodup_outside (c : Case) (args : List (Option Lexical)) : (outside c args).Nodup := by
  rcases args with _ | ⟨_ | _, _⟩ <;> simp [outside, highestCase]

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

/-- The formula and the language's setting fix how many accusatives a verb assigns, and among the
logically possible derivations with that many, the derivations are those in which every moved
argument takes the shortest path. -/
theorem mem_derivations_iff (hc : c.IsFunctional) :
    d ∈ derivations a c args ↔ ∃ n ∈ a.counts (maxAcc args).toNat,
      MinimalFor (Candidate (outside c args) n args) pathLength d := by
  rw [mem_derivations]
  refine exists_congr fun n ↦ and_congr_right fun hn ↦ ?_
  have hle := Assignment.le_of_mem_counts hn
  rw [toNat_maxAcc] at hle
  rw [minimalFor_pathLength_iff (isFunctional_of_mem_outside hc args) (nodup_outside c args)
    (by omega), eq_comm]

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

-- economy, not the formula, excludes a lower argument moving past a higher one
theorem economy_excludes :
    Candidate [.nom, .obj] 1 [none, none, none] [.nom, .acc, .obj] ∧
      ¬ MinimalFor (Candidate [.nom, .obj] 1 [none, none, none]) pathLength [.nom, .acc, .obj] ∧
      [.nom, .obj, .acc] ∈ derivations .optional .obj [none, none, none] := by
  refine ⟨⟨by simp [Slot, Case.IsFunctional], by decide, by decide⟩, ?_, by decide⟩
  rw [minimalFor_pathLength_iff (by decide) (by decide) (by decide)]
  decide

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

-- p. 204: the strong interpretation, `.lacking` under a lexical subject, fails where (24b) succeeds
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
