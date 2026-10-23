module

public import Mathlib.Logic.Function.Basic

/-!
# Resolution rules

This file defines resolution rules, which give the agreement form of a coordination from
its conjuncts, and their application in order.

A resolution rule is of one of two types: at least one conjunct is of a sort (type A), or every
conjunct is (type B), and the rule then selects a form; the logically possible type referring to
a majority of the conjuncts is unattested. A language's rules are ordered, the first that
applies selects the form, and a coordination to which no rule applies has no resolved form, an
ineffable coordination. The final rule is often unconditional, an "otherwise" clause, and then
every coordination has a form. The sort may be read off the conjuncts' gender, a syntactic rule,
or their meaning, a semantic rule; the descriptor type is a parameter.

Rules of both types see only which descriptors occur among the conjuncts, never how many
conjuncts bear one, so they cannot count: number resolution, which gives two singulars the dual
and three the plural, is not of this form.

## Main definitions

* `Agreement.ResolutionRule`: a rule, of type A (`any`) or type B (`all`), with its sort and
  the form it selects.
* `Agreement.ResolutionRule.Applies`: whether a rule applies to a list of conjuncts.
* `Agreement.ResolutionRule.resolve`: the form the first applicable rule of an ordered list
  selects.

## Main results

* `Agreement.ResolutionRule.resolve_congr`: resolution depends only on which descriptors occur
  among the conjuncts.
* `Agreement.ResolutionRule.resolve_any_otherwise`: a type-A rule and its default are the
  type-B rule for the complementary sort with the two forms swapped.
* `Agreement.ResolutionRule.resolve_factorsThrough`: rules reading their sorts through a map
  resolve through it.

## References

* [corbett-1991] — chapter 9; the two types, §9.4, pp. 279–280, and §9.6, p. 290
* [givon-1970] — the resolution of gender conflicts in Bantu
* [corbett-2006] — the standard monograph on agreement
-/

@[expose] public section

namespace Agreement

/-- A resolution rule: at least one conjunct (`any`) or every conjunct (`all`) of a sort, and
the form it selects. -/
inductive ResolutionRule (α G : Type*) where
  /-- The type-A rule: some conjunct is of the sort `p`. -/
  | any (p : α → Prop) [DecidablePred p] (g : G)
  /-- The type-B rule: every conjunct is of the sort `p`. -/
  | all (p : α → Prop) [DecidablePred p] (g : G)

namespace ResolutionRule

variable {α β G : Type*}

/-- The sort a rule asks of its conjuncts. -/
def pred : ResolutionRule α G → α → Prop
  | any p _ | all p _ => p

/-- The form a rule selects. -/
def out : ResolutionRule α G → G
  | any _ g | all _ g => g

/-- Whether the rule applies to a coordination. -/
def Applies : ResolutionRule α G → List α → Prop
  | any p _, cs => ∃ c ∈ cs, p c
  | all p _, cs => ∀ c ∈ cs, p c

instance : ∀ (r : ResolutionRule α G) (cs : List α), Decidable (r.Applies cs)
  | any p _, cs => inferInstanceAs (Decidable (∃ c ∈ cs, p c))
  | all p _, cs => inferInstanceAs (Decidable (∀ c ∈ cs, p c))

/-- The unconditional final rule. -/
def otherwise (g : G) : ResolutionRule α G := all (fun _ ↦ True) g

variable {p q : α → Prop} [DecidablePred p] [DecidablePred q] {g : G} {cs ds : List α}

@[simp] theorem out_any : (any p g).out = g := rfl
@[simp] theorem out_all : (all p g).out = g := rfl
@[simp] theorem out_otherwise : (otherwise g : ResolutionRule α G).out = g := rfl

@[simp] theorem applies_any : (any p g).Applies cs ↔ ∃ c ∈ cs, p c := .rfl
@[simp] theorem applies_all : (all p g).Applies cs ↔ ∀ c ∈ cs, p c := .rfl

@[simp] theorem applies_otherwise : (otherwise g : ResolutionRule α G).Applies cs :=
  fun _ _ ↦ trivial

theorem applies_congr (r : ResolutionRule α G) (h : ∀ c, c ∈ cs ↔ c ∈ ds) :
    r.Applies cs ↔ r.Applies ds := by
  cases r <;> simp [h]

/-- Apply ordered rules: the first that applies selects the form; none applying, the
coordination has no resolved form. -/
def resolve (rs : List (ResolutionRule α G)) (cs : List α) : Option G :=
  (rs.find? (·.Applies cs)).map out

variable {r : ResolutionRule α G} {rs rs' : List (ResolutionRule α G)}

@[simp] theorem resolve_nil : resolve ([] : List (ResolutionRule α G)) cs = none := rfl

theorem resolve_cons :
    resolve (r :: rs) cs = if r.Applies cs then some r.out else resolve rs cs := by
  by_cases h : r.Applies cs <;> simp [resolve, h]

@[simp] theorem resolve_cons_of_applies (h : r.Applies cs) : resolve (r :: rs) cs = some r.out := by
  simp [resolve_cons, h]

@[simp] theorem resolve_cons_of_not_applies (h : ¬ r.Applies cs) :
    resolve (r :: rs) cs = resolve rs cs := by
  simp [resolve_cons, h]

theorem resolve_append : resolve (rs ++ rs') cs = (resolve rs cs).or (resolve rs' cs) := by
  simp [resolve, List.find?_append, Option.map_or]

@[simp] theorem resolve_eq_none_iff : resolve rs cs = none ↔ ∀ r ∈ rs, ¬ r.Applies cs := by
  simp [resolve]

@[simp] theorem resolve_isSome_iff : (resolve rs cs).isSome ↔ ∃ r ∈ rs, r.Applies cs := by
  simp [resolve]

theorem mem_map_out_of_resolve_eq_some (h : resolve rs cs = some g) : g ∈ rs.map out := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact List.mem_map_of_mem (List.mem_of_find?_eq_some hr)

theorem resolve_append_otherwise_isSome : (resolve (rs ++ [otherwise g]) cs).isSome :=
  resolve_isSome_iff.mpr ⟨otherwise g, by simp, applies_otherwise⟩

theorem resolve_congr_of_applies_iff (h : ∀ r ∈ rs, r.Applies cs ↔ r.Applies ds) :
    resolve rs cs = resolve rs ds := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.forall_mem_cons] at h
    simp [resolve_cons, h.1, ih h.2]

/-- Resolution depends only on which descriptors occur among the conjuncts, so rules cannot
count them. -/
theorem resolve_congr (rs : List (ResolutionRule α G)) (h : ∀ c, c ∈ cs ↔ c ∈ ds) :
    resolve rs cs = resolve rs ds :=
  resolve_congr_of_applies_iff fun r _ ↦ r.applies_congr h

/-- A type-A rule with its default is the type-B rule for the complementary sort with the
default swapped. -/
theorem resolve_any_otherwise {a b : G} (h : ∀ c, q c ↔ ¬ p c) :
    resolve [any p a, otherwise b] cs = resolve [all q b, otherwise a] cs := by
  by_cases hp : ∀ c ∈ cs, ¬ p c <;> simp +contextual [resolve_cons, h, hp]

/-- Rules whose sorts read the conjuncts through `f` give a resolution reading them through
`f`. -/
theorem resolve_factorsThrough {f : α → β} (h : ∀ r ∈ rs, Function.FactorsThrough r.pred f) :
    Function.FactorsThrough (resolve rs) (List.map f) := fun cs ds hcd ↦
  resolve_congr_of_applies_iff fun r hr ↦ by
    have e c := ((h r hr).extend_apply (fun _ ↦ False) c).symm
    cases r <;> simp only [pred] at e <;> simp only [applies_any, applies_all, e]
    · simpa using congrArg (∃ y ∈ ·, Function.extend f _ (fun _ ↦ False) y) hcd
    · simpa using congrArg (∀ y ∈ ·, Function.extend f _ (fun _ ↦ False) y) hcd

end ResolutionRule

end Agreement
