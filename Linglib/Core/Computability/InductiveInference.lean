/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Stream.Init
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Language identification in the limit

A learner sees the strings of an unknown language one at a time, in any order, with repetitions
and pauses, and after each presentation conjectures a language. It identifies the language in the
limit if on every such presentation its conjectures are eventually the language itself. A class of
languages over a countable set of strings is identifiable
[exactly when it is countable and its languages have
telltales](##InductiveInference.identifiable_iff), a telltale of a language being a finite subset
that no member of the class properly inside the language contains. Hence
[no class containing an infinite language and all its finite subsets is
identifiable](##InductiveInference.not_identifiable_of_finite_subsets), nor
[any class containing a strictly increasing chain of languages and its
union](##InductiveInference.not_identifiable_of_strictMono_iUnion).

## Implementation notes

The characterization is the ineffective one: a learner is any function on finite sequences,
computable or not, and conjectures a language rather than a name for one, the two coming to the
same when effectiveness is not required. Effective inference of an indexed family of recursive
languages further needs the telltales to be uniformly enumerable, which is not formalized.
A pause lets the empty language have a text; on nonempty languages pauses change nothing, since
a learner can treat a pause as a repetition of the previous string. The strings form an arbitrary
countable type, the words over an alphabet being one instance.

## References

* [gold-1967]
* [angluin-1980]
-/

@[expose] public section

open Filter Set

namespace InductiveInference

variable {α : Type*}

/-- A **text** presents strings one at a time, `none` being a pause in which nothing is
presented. -/
abbrev Text (α : Type*) := Stream' (Option α)

/-- The strings occurring in a finite sequence of presentations. -/
def content (σ : List (Option α)) : Set α := {x | some x ∈ σ}

/-- The strings occurring in a text. A text **for** `L` is one whose content is `L`. -/
def Text.content (t : Text α) : Set α := {x | some x ∈ t}

/-- A learner conjectures a language from each finite sequence of presentations. -/
abbrev Learner (α : Type*) := List (Option α) → Set α

/-- `φ` **identifies** `L` **in the limit** when on every text for `L` its conjectures are
eventually `L`. -/
def Identifies (φ : Learner α) (L : Set α) : Prop :=
  ∀ t : Text α, t.content = L → ∀ᶠ n in atTop, φ (t.take n) = L

/-- A class of languages is **identifiable in the limit** when one learner identifies each of its
languages. -/
def Identifiable (𝓛 : Set (Set α)) : Prop :=
  ∃ φ : Learner α, ∀ L ∈ 𝓛, Identifies φ L

/-- `T` is a **telltale** of `L` in `𝓛`: a finite subset of `L` that no language of `𝓛` properly
inside `L` contains. Once `T` has been presented, conjecturing `L` cannot overgeneralize. -/
def IsTelltale (𝓛 : Set (Set α)) (L T : Set α) : Prop :=
  T.Finite ∧ T ⊆ L ∧ ∀ L' ∈ 𝓛, T ⊆ L' → ¬L' ⊂ L

/-! ### Content -/

theorem content_finite (σ : List (Option α)) : (content σ).Finite :=
  (σ.finite_toSet.preimage (Option.some_injective α).injOn).subset fun _ h ↦ h

@[simp] theorem mem_content {σ : List (Option α)} {x : α} : x ∈ content σ ↔ some x ∈ σ := Iff.rfl

@[simp] theorem content_nil : content ([] : List (Option α)) = ∅ := by simp [content]

@[simp] theorem content_append (σ τ : List (Option α)) :
    content (σ ++ τ) = content σ ∪ content τ := by
  ext; simp [content]

@[simp] theorem content_singleton_some (x : α) : content [some x] = {x} := by
  ext; simp [content, eq_comm]

@[simp] theorem content_singleton_none : content [(none : Option α)] = ∅ := by
  ext; simp [content]

/-- Every finite set is the content of a finite sequence. -/
theorem exists_content_eq {T : Set α} (hT : T.Finite) : ∃ σ : List (Option α), content σ = T := by
  obtain ⟨l, rfl⟩ := hT.exists_finset_coe.elim fun s hs ↦ (⟨s.toList, by simp [← hs]⟩ :
    ∃ l : List α, {x | x ∈ l} = T)
  exact ⟨l.map some, by ext; simp [content]⟩

namespace Text

theorem content_take_subset (t : Text α) (n : ℕ) :
    InductiveInference.content (t.take n) ⊆ t.content :=
  fun x hx ↦ by
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem (mem_content.mp hx)
    have hn : k < n := by simpa using hk
    have := Stream'.getElem?_take (s := t) hn
    rw [List.getElem?_eq_getElem hk, hkx] at this
    exact ⟨k, by simpa using this⟩

/-- Every finite part of a text has been presented after finitely many steps. -/
theorem eventually_subset_content_take {t : Text α} {T : Set α} (hT : T.Finite)
    (hsub : T ⊆ t.content) : ∀ᶠ n in atTop, T ⊆ InductiveInference.content (t.take n) := by
  simp only [Set.subset_def]
  refine (eventually_all_finite hT).mpr fun x hx ↦ ?_
  obtain ⟨k, hk⟩ := hsub hx
  filter_upwards [eventually_gt_atTop k] with n hn
  have := Stream'.getElem?_take (s := t) hn
  rw [← hk] at this
  exact mem_content.mpr (List.mem_of_getElem? this)

theorem content_appendStream (σ : List (Option α)) (t : Text α) :
    Text.content (σ ++ₛ t) = InductiveInference.content σ ∪ t.content := by
  induction σ with
  | nil => simp
  | cons a l ih =>
    ext x
    have hcons : some x ∈ a :: l ++ₛ t ↔ some x = a ∨ some x ∈ l ++ₛ t := by
      refine ⟨fun ⟨n, hn⟩ ↦ ?_, ?_⟩
      · rcases n with _ | n
        · exact .inl hn
        · exact .inr ⟨n, hn⟩
      · rintro (h | ⟨n, hn⟩)
        · exact ⟨0, h⟩
        · exact ⟨n + 1, hn⟩
    have hmem : x ∈ Text.content (l ++ₛ t) ↔ x ∈ InductiveInference.content l ∪ t.content := by
      rw [ih]
    change some x ∈ a :: l ++ₛ t ↔ some x ∈ a :: l ∨ x ∈ t.content
    rw [hcons, List.mem_cons, or_assoc]
    exact or_congr_right hmem

theorem take_appendStream (σ : List (Option α)) (t : Text α) (m : ℕ) :
    (σ ++ₛ t).take (σ.length + m) = σ ++ t.take m := by
  induction σ with
  | nil => simp
  | cons a l ih => rw [List.length_cons, Nat.succ_add, Stream'.cons_append_stream,
      Stream'.take_succ_cons, ih, List.cons_append]

/-- Every language over a countable set of strings has a text. -/
theorem exists_content_eq [Countable α] (L : Set α) : ∃ t : Text α, t.content = L := by
  rcases L.eq_empty_or_nonempty with rfl | hL
  · exact ⟨fun _ ↦ none, eq_empty_of_forall_notMem fun x ⟨n, hn⟩ ↦ by simp [Stream'.get] at hn⟩
  · obtain ⟨g, rfl⟩ := L.to_countable.exists_eq_range hL
    refine ⟨fun n ↦ some (g n), Set.ext fun x ↦ ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩⟩
    · exact (Option.some_injective α hn).symm
    · exact congrArg some hn.symm

/-- A prefix-increasing chain of finite sequences of unbounded length has a limit text. -/
private theorem exists_take_eq (σ : ℕ → List (Option α)) (hpre : ∀ n, σ n <+: σ (n + 1))
    (hlen : ∀ n, n ≤ (σ n).length) : ∃ t : Text α, ∀ n, t.take (σ n).length = σ n := by
  have hmono : ∀ {a b}, a ≤ b → σ a <+: σ b := fun {a b} hab ↦ by
    induction b, hab using Nat.le_induction with
    | base => exact List.prefix_rfl
    | succ b _ ih => exact ih.trans (hpre b)
  refine ⟨fun m ↦ (σ (m + 1)).getD m none, fun n ↦ ?_⟩
  refine List.ext_getElem (Stream'.length_take _ _) fun m h₁ h₂ ↦ ?_
  have hm : m < (σ (m + 1)).length := hlen (m + 1)
  have key : (σ (m + 1))[m] = (σ n)[m] := by
    rcases le_total n (m + 1) with h | h
    · exact ((hmono h).getElem h₂).symm
    · exact (hmono h).getElem hm
  have htake := Stream'.getElem?_take (s := fun m ↦ (σ (m + 1)).getD m none)
    (show m < (σ n).length from h₂)
  rw [List.getElem?_eq_getElem h₁] at htake
  rw [Option.some_inj.mp htake, ← key]
  simp [Stream'.get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]

/-- If a property of finite sequences can always be reached by extending within `L`, some text for
`L` meets it infinitely often: the text the proofs of Gold and of Angluin build. -/
theorem exists_frequently {L : Set α} {P : List (Option α) → Prop} {e : Text α}
    (he : e.content = L)
    (hP : ∀ σ, InductiveInference.content σ ⊆ L →
      ∃ τ, InductiveInference.content τ ⊆ L ∧ P (σ ++ τ)) :
    ∃ t : Text α, t.content = L ∧ ∃ᶠ n in atTop, P (t.take n) := by
  have hext : ∀ (n : ℕ) (σ : {σ : List (Option α) // InductiveInference.content σ ⊆ L}),
      ∃ σ' : {σ : List (Option α) // InductiveInference.content σ ⊆ L},
        σ.1 ++ [e n] <+: σ'.1 ∧ P σ'.1 := fun n ⟨σ, hσ⟩ ↦ by
    have hstep : InductiveInference.content (σ ++ [e n]) ⊆ L := by
      rw [content_append]
      refine union_subset hσ fun x hx ↦ ?_
      have : e n = some x := by simpa [mem_content, eq_comm] using hx
      exact he ▸ ⟨n, this.symm⟩
    obtain ⟨τ, hτ, hPτ⟩ := hP _ hstep
    exact ⟨⟨_, by rw [content_append]; exact union_subset hstep hτ⟩, List.prefix_append _ _, hPτ⟩
  choose next hnext hPnext using hext
  let σ : ℕ → {σ : List (Option α) // InductiveInference.content σ ⊆ L} :=
    fun n ↦ Nat.rec ⟨[], by simp⟩ (fun k s ↦ next k s) n
  have hstep : ∀ n, (σ n).1 ++ [e n] <+: (σ (n + 1)).1 := fun n ↦ hnext n (σ n)
  have hpre : ∀ n, (σ n).1 <+: (σ (n + 1)).1 := fun n ↦
    (List.prefix_append _ _).trans (hstep n)
  have hlen : ∀ n, n ≤ (σ n).1.length := fun n ↦ by
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have := (hstep k).length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
  obtain ⟨t, ht⟩ := exists_take_eq (fun n ↦ (σ n).1) hpre hlen
  refine ⟨t, Set.Subset.antisymm (fun x ⟨k, hk⟩ ↦ ?_) fun x hx ↦ ?_, ?_⟩
  · have hk' : k < (σ (k + 1)).1.length := hlen (k + 1)
    refine (σ (k + 1)).2 ?_
    have := Stream'.getElem?_take (s := t) hk'
    rw [ht (k + 1), ← hk] at this
    exact mem_content.mpr (List.mem_of_getElem? this)
  · rw [← he] at hx
    obtain ⟨n, hn⟩ := hx
    have hmem : some x ∈ (σ (n + 1)).1 :=
      (hstep n).subset (by simp [← show e n = some x from hn.symm])
    rw [← ht (n + 1)] at hmem
    exact content_take_subset t _ (mem_content.mpr hmem)
  · refine frequently_atTop.mpr fun N ↦ ⟨(σ (N + 1)).1.length, (by have := hlen (N + 1); omega), ?_⟩
    rw [ht (N + 1)]
    exact hPnext N (σ N)

end Text

/-! ### The characterization -/

theorem Identifiable.mono {𝓛 𝓜 : Set (Set α)} (h : 𝓛 ⊆ 𝓜) (hm : Identifiable 𝓜) :
    Identifiable 𝓛 :=
  hm.imp fun _ hφ L hL ↦ hφ L (h hL)

/-- A learner identifying each language of `𝓛` gives each of them a telltale, the content of a
finite sequence after which it can no longer be moved off `L`. -/
theorem exists_isTelltale [Countable α] {𝓛 : Set (Set α)} {φ : Learner α}
    (hφ : ∀ L ∈ 𝓛, Identifies φ L) {L : Set α} (hL : L ∈ 𝓛) : ∃ T, IsTelltale 𝓛 L T := by
  by_contra hno
  have hno' : ∀ T : Set α, T.Finite → T ⊆ L → ∃ L' ∈ 𝓛, T ⊆ L' ∧ L' ⊂ L := fun T hT hTL ↦ by
    by_contra h
    exact hno ⟨T, hT, hTL, fun L' hL' hTL' hss ↦ h ⟨L', hL', hTL', hss⟩⟩
  obtain ⟨e, he⟩ := Text.exists_content_eq L
  obtain ⟨t, ht, hfreq⟩ := Text.exists_frequently (P := fun σ ↦ φ σ ≠ L) he fun σ hσ ↦ by
    obtain ⟨L', hL', hσL', hssub⟩ := hno' _ (content_finite σ) hσ
    obtain ⟨t', ht'⟩ := Text.exists_content_eq L'
    have htext : Text.content (σ ++ₛ t') = L' := by
      rw [Text.content_appendStream, ht', union_eq_right.mpr hσL']
    obtain ⟨n, hφn, hn⟩ := ((hφ L' hL' _ htext).and (eventually_ge_atTop σ.length)).exists
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine ⟨t'.take m, (Text.content_take_subset t' m).trans (ht' ▸ hssub.subset), ?_⟩
    rw [← Text.take_appendStream, hφn]
    exact hssub.ne
  exact hfreq (hφ L hL t ht |>.mono fun _ h hne ↦ hne h)

/-- A countable class whose languages have telltales is identifiable, by conjecturing the first
language in an enumeration whose telltale has appeared and which contains the data. -/
theorem identifiable_of_isTelltale {𝓛 : Set (Set α)} (hc : 𝓛.Countable)
    (hT : ∀ L ∈ 𝓛, ∃ T, IsTelltale 𝓛 L T) : Identifiable 𝓛 := by
  classical
  rcases 𝓛.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ ∅, by simp⟩
  obtain ⟨A, rfl⟩ := hc.exists_eq_range hne
  choose T hT using fun i ↦ hT (A i) (mem_range_self i)
  refine ⟨fun σ ↦ if h : ∃ i, T i ⊆ content σ ∧ content σ ⊆ A i then A (Nat.find h) else ∅, ?_⟩
  rintro L ⟨z', rfl⟩ t ht
  have hz : ∃ z, A z = A z' := ⟨z', rfl⟩
  have hAz : A (Nat.find hz) = A z' := Nat.find_spec hz
  have h₁ : ∀ᶠ n in atTop, T (Nat.find hz) ⊆ content (t.take n) :=
    Text.eventually_subset_content_take (hT _).1
      (((hT _).2.1.trans hAz.subset).trans ht.symm.subset)
  have h₂ : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (Nat.find hz),
      ¬(T i ⊆ content (t.take n) ∧ content (t.take n) ⊆ A i) := by
    refine (Finset.eventually_all _).mpr fun i hi ↦ ?_
    by_cases hsub : A z' ⊆ A i
    · refine .of_forall fun n ⟨hTi, _⟩ ↦ (hT i).2.2 _ (mem_range_self z')
        (hTi.trans ((t.content_take_subset n).trans ht.subset))
        (hsub.ssubset_of_ne (Ne.symm (Nat.find_min hz (Finset.mem_range.mp hi))))
    · obtain ⟨x, hx, hxi⟩ := not_subset.mp hsub
      filter_upwards [Text.eventually_subset_content_take (finite_singleton x)
        (singleton_subset_iff.mpr (ht ▸ hx))] with n hn ⟨_, hsub'⟩
      exact hxi (hsub' (hn rfl))
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  have hcsub : content (t.take n) ⊆ A (Nat.find hz) := by
    rw [hAz, ← ht]; exact t.content_take_subset n
  have hex : ∃ i, T i ⊆ content (t.take n) ∧ content (t.take n) ⊆ A i := ⟨_, hn₁, hcsub⟩
  have hfind : Nat.find hex = Nat.find hz :=
    (Nat.find_eq_iff hex).mpr ⟨⟨hn₁, hcsub⟩, fun i hi ↦ hn₂ i (Finset.mem_range.mpr hi)⟩
  simp only [hex, ↓reduceDIte, hfind, hAz]

/-- A class of languages over a countable set of strings is identifiable in the limit exactly when
it is countable and each of its languages has a telltale. Angluin's condition without its
effectiveness requirement, and Gold's observation that only countably many conjectures exist. -/
theorem identifiable_iff [Countable α] {𝓛 : Set (Set α)} :
    Identifiable 𝓛 ↔ 𝓛.Countable ∧ ∀ L ∈ 𝓛, ∃ T, IsTelltale 𝓛 L T :=
  ⟨fun ⟨φ, hφ⟩ ↦ ⟨(countable_range φ).mono fun L hL ↦ by
      obtain ⟨t, ht⟩ := Text.exists_content_eq L
      obtain ⟨n, hn⟩ := (hφ L hL t ht).exists
      exact ⟨_, hn⟩, fun _ hL ↦ exists_isTelltale hφ hL⟩,
    fun h ↦ identifiable_of_isTelltale h.1 h.2⟩

/-- Every finite class is identifiable. -/
theorem identifiable_of_finite {𝓛 : Set (Set α)} (h : 𝓛.Finite) : Identifiable 𝓛 := by
  refine identifiable_of_isTelltale h.countable fun L _ ↦ ?_
  have hx : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ⊂ L}, ∃ x, x ∈ L ∧ x ∉ L'.1 :=
    fun L' ↦ exists_of_ssubset L'.2.2
  choose x hxL hxL' using hx
  have : Finite {L' // L' ∈ 𝓛 ∧ L' ⊂ L} :=
    (h.subset fun _ hL' ↦ hL'.1 : {L' | L' ∈ 𝓛 ∧ L' ⊂ L}.Finite).to_subtype
  exact ⟨range x, finite_range x, range_subset_iff.mpr hxL,
    fun L' hL' hT hss ↦ hxL' ⟨L', hL', hss⟩ (hT ⟨_, rfl⟩)⟩

/-- **Gold's theorem**: a class containing an infinite language and all its finite subsets is not
identifiable from text. In particular no class containing every finite language and an infinite
one is. -/
theorem not_identifiable_of_finite_subsets [Countable α] {𝓛 : Set (Set α)} {L : Set α}
    (hL : L ∈ 𝓛) (hinf : L.Infinite) (hfin : ∀ T ⊆ L, T.Finite → T ∈ 𝓛) : ¬Identifiable 𝓛 :=
  fun h ↦ by
    obtain ⟨T, hT, hTL, hno⟩ := (identifiable_iff.mp h).2 L hL
    exact hno T (hfin T hTL hT) subset_rfl (hTL.ssubset_of_ne fun e ↦ hinf (e ▸ hT))

/-- A class containing a strictly increasing chain of languages and its union is not identifiable
from text, since the finite telltale of the union would already lie in a member of the chain. -/
theorem not_identifiable_of_strictMono_iUnion [Countable α] {𝓛 : Set (Set α)} {A : ℕ → Set α}
    (hA : StrictMono A) (hmem : ∀ n, A n ∈ 𝓛) (hU : ⋃ n, A n ∈ 𝓛) : ¬Identifiable 𝓛 := fun h ↦ by
  obtain ⟨T, hT, hTU, hno⟩ := (identifiable_iff.mp h).2 _ hU
  have hev : ∀ᶠ n in atTop, ∀ x ∈ T, x ∈ A n := (eventually_all_finite hT).mpr fun x hx ↦ by
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hTU hx)
    filter_upwards [eventually_ge_atTop m] with n hn using hA.monotone hn hm
  obtain ⟨n, hn⟩ := hev.exists
  exact hno _ (hmem n) hn ((hA (Nat.lt_succ_self n)).trans_subset (subset_iUnion A _))

end InductiveInference
