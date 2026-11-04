module

public import Linglib.Semantics.Composition.Tree

/-!
# Readings of an ambiguous lexicon

A word may have several available readings. A resolution of a tree chooses one reading for each
occurrence of a word, and [the readings of the tree](##readings) are the values the engine computes
over its resolutions. The engine on a lexicon with one reading per word
[is the special case](##readings_eq_of_choice), and a binary phrase's readings
[are the pointwise compositions of its daughters'](##mem_readings_phrase_binary). Under the set
effect an abstraction chooses a reading at each entity instead, so [a tree's readings are among the
values the engine computes under that effect](##mem_interp_setM_of_mem_readings).

## References

* [kratzer-shimoyama-2002]
* [charlow-2020]
-/

@[expose] public section

namespace PhraseStructure.Tree

open Montague
open scoped Assignment

/-! ### Readings -/

section Readings

variable {C : Type} {L : Type*} {E W : Type} {S : Sorts} {M : Type → Type} [Applicative M]
  [Distributive M]

theorem interp_map {L' : Type*} (lex : L' → Option (Denotation E W M S)) (f : L → L')
    (g : Assignment E) (t : Tree C L) : interp lex g (t.map f) = interp (lex ∘ f) g t := by
  simp only [interp, translate_map]

variable (lex : L → Set (Denotation E W M S)) (g : Assignment E)

/-- The readings of a tree when each word has a set of readings are the denotations of the trees
obtained by resolving each occurrence of a word to one of its readings. -/
def readings (t : Tree C L) : Set (Denotation E W M S) :=
  {d | ∃ r : Tree C {p : L × Denotation E W M S // p.2 ∈ lex p.1},
    r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d}

variable {lex g}

theorem exists_resolution_of_interp {choice : L → Option (Denotation E W M S)} {t : Tree C L}
    {d : Denotation E W M S} (h : interp choice g t = some d) :
    ∃ r : Tree C {p : L × Denotation E W M S // choice p.1 = some p.2},
      r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d := by
  induction t using Tree.rec' generalizing g d with
  | terminal c w =>
    rw [interp_terminal] at h
    exact ⟨.terminal c ⟨(w, d), h⟩, rfl, by rw [interp_terminal]⟩
  | phrase c k cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp, translate])
    | [t] =>
      obtain ⟨r, hr, hd⟩ := ih t (by simp) h
      exact ⟨.phrase c k (r :: []), by simp [hr], hd⟩
    | [t₁, t₂] =>
      rw [interp_phrase_binary] at h
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, hd₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨r₂, hr₂, hd₂⟩ := ih t₂ (by simp) h₂
      exact ⟨.phrase c k (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
        by rw [interp_phrase_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp, translate])
  | trace n c => exact ⟨.trace n c, rfl, h⟩
  | bind n c body ih =>
    rw [interp_bind] at h
    obtain ⟨⟨τ, probe⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hd⟩ := ih hb
    have hres : ∀ g', interp choice g' body = interp (fun p ↦ some p.1.2) g' r := fun g' ↦ by
      rw [← hr, interp_map]
      exact congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g') r
    refine ⟨.bind n c r, by simp [hr], ?_⟩
    rw [interp_bind, hd, Option.bind_some]
    simpa only [hres] using h
  | junk l cs hj _ => exact absurd h (by rw [interp_junk _ _ hj]; simp)

theorem interp_mem_readings {choice : L → Option (Denotation E W M S)}
    (hc : ∀ w d, choice w = some d → d ∈ lex w) {t : Tree C L} {d : Denotation E W M S}
    (h : interp choice g t = some d) : d ∈ readings lex g t := by
  obtain ⟨r, hr, hd⟩ := exists_resolution_of_interp h
  refine ⟨r.map fun p ↦ ⟨p.1, hc _ _ p.2⟩, ?_, ?_⟩
  · rw [Tree.map_map]; exact hr
  · rw [interp_map]; exact hd

/-- On a lexicon with one reading per word, the readings are the engine's values. -/
theorem readings_eq_of_choice (choice : L → Option (Denotation E W M S)) (t : Tree C L) :
    readings (fun w ↦ {d | choice w = some d}) g t = {d | interp choice g t = some d} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ interp_mem_readings (fun _ _ h ↦ h) h⟩
  show interp choice g t = some d
  rw [← hr, interp_map]
  exact (congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g) r).trans hd

@[simp] theorem readings_terminal (c : C) (w : L) : readings lex g (.terminal c w) = lex w := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.terminal c ⟨(w, d), h⟩, rfl, rfl⟩⟩
  obtain ⟨p, rfl, rfl⟩ := Tree.map_eq_terminal_iff.1 hr
  cases Option.some.inj hd
  exact p.2

@[simp] theorem readings_trace (n : ℕ) (c : C) :
    readings lex g (.trace n c) = {⟨.e, pure (g n)⟩} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.trace n c, rfl, h ▸ rfl⟩⟩
  obtain rfl := Tree.map_eq_trace_iff.1 hr
  exact (Option.some.inj hd).symm

/-- A binary phrase's readings are the pointwise compositions of its daughters'. -/
theorem mem_readings_phrase_binary {c : C} {k : PhraseKind} {t₁ t₂ : Tree C L}
    {d : Denotation E W M S} :
    d ∈ readings lex g (.phrase c k (t₁ :: t₂ :: [])) ↔
      ∃ d₁ ∈ readings lex g t₁, ∃ d₂ ∈ readings lex g t₂,
        Mode.combine? Mode.evalM d₁ d₂ = some d := by
  constructor
  · rintro ⟨r, hr, hd⟩
    obtain ⟨cs, rfl, hcs⟩ := Tree.map_eq_phrase_iff.1 hr
    obtain ⟨r₁, cs₁, rfl, rfl, hcs₁⟩ := List.map_eq_cons_iff.mp hcs
    obtain ⟨r₂, cs₂, rfl, rfl, hcs₂⟩ := List.map_eq_cons_iff.mp hcs₁
    obtain rfl := List.map_eq_nil_iff.mp hcs₂
    rw [interp_phrase_binary] at hd
    obtain ⟨d₁, h₁, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨d₂, h₂, hd⟩ := Option.bind_eq_some_iff.mp hd
    exact ⟨d₁, ⟨r₁, rfl, h₁⟩, d₂, ⟨r₂, rfl, h₂⟩, hd⟩
  · rintro ⟨d₁, ⟨r₁, hr₁, hd₁⟩, d₂, ⟨r₂, hr₂, hd₂⟩, h⟩
    exact ⟨.phrase c k (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
      by rw [interp_phrase_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩

/-- A binder's readings interpret it over a resolution of its body, which reads each occurrence
the same way at every value of the bound variable. -/
theorem mem_readings_bind {n : ℕ} {c : C} {t : Tree C L} {d : Denotation E W M S} :
    d ∈ readings lex g (.bind n c t) ↔ ∃ r : Tree C {p : L × Denotation E W M S // p.2 ∈ lex p.1},
      r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g (.bind n c r) = some d := by
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun ⟨r, hr, hd⟩ ↦ ⟨.bind n c r, by rw [Tree.map_bind, hr], hd⟩⟩
  obtain ⟨b, rfl, hb⟩ := Tree.map_eq_bind_iff.1 hr
  exact ⟨b, hb, hd⟩

end Readings

/-! ### Readings and the set effect

Resolving each occurrence of a word before interpretation, as `readings` does, chooses one reading
for every entity an abstraction ranges over. Under the set effect an abstraction chooses a reading
at each entity (`SetM.mem_run_distribute`), so the readings of a tree are among the values the
engine computes for it under the set effect. -/

section SetEffect

variable {C : Type} {L : Type*} {E W : Type} {S : Sorts}

/-- The readings of a word under a set-valued lexicon: its denotations at each of its values. -/
def wordReadings (lex : L → Option (Denotation E W SetM S)) (w : L) : Set (Denotation E W Id S) :=
  {d | ∃ X, lex w = some ⟨d.1, X⟩ ∧ d.2 ∈ X.run}

/-- The readings of a tree under the readings of a set-valued lexicon's words are among the values
the engine computes for it under the set effect. -/
theorem mem_interp_setM_of_mem_readings (lex : L → Option (Denotation E W SetM S))
    (g : Assignment E) {t : Tree C L} {d : Denotation E W Id S}
    (hd : d ∈ readings (wordReadings lex) g t) :
    ∃ X, interp lex g t = some ⟨d.1, X⟩ ∧ d.2 ∈ X.run := by
  obtain ⟨r, rfl, hr⟩ := hd
  rw [interp_map]
  simp only [interp] at hr ⊢
  obtain ⟨⟨τ, u⟩, hu, hev⟩ := Option.map_eq_some_iff.1 hr
  have hrel : ∀ (p : {p : L × Denotation E W Id S //
      p.2 ∈ wordReadings lex p.1}) d',
      (lex ∘ fun x ↦ x.1.1) p = some d' →
        ∃ c, some p.1.2 = some ⟨d'.1, c⟩ ∧ c ∈ SetM.run d'.2 := by
    rintro ⟨⟨w, ⟨τ', c⟩⟩, X, hX, hc⟩ d' hd'
    simp only [Function.comp_apply, hX, Option.some.injEq] at hd'
    subst hd'
    exact ⟨c, rfl, hc⟩
  have htypes : (translate individualIndices (lex ∘ fun x ↦ x.1.1) r).map (·.1) = some τ := by
    rw [← translate_map_fst (lex := fun p ↦ some p.1.2) (fun p ↦ ?_) r, hu]
    · rfl
    · obtain ⟨⟨w, ⟨τ', c⟩⟩, X, hX, -⟩ := p
      simp [hX]
  obtain ⟨⟨τ', u'⟩, hu', hτ⟩ := Option.map_eq_some_iff.1 htypes
  subst hτ
  obtain ⟨u₀, hu₀, hR⟩ :=
    translate_rel (R := fun _ c c' ↦ c ∈ SetM.run c') (fun p ↦ some p.1.2) hrel r hu'
  rw [hu, Option.some.injEq, Sigma.mk.injEq] at hu₀
  obtain ⟨-, hu₀⟩ := hu₀
  obtain rfl := eq_of_heq hu₀
  have hmem := hR.mem_run_evalM g
  simp only [evalAt, Term.evalM_id] at hev
  subst hev
  exact ⟨_, by rw [hu', Option.map_some], hmem⟩

end SetEffect

end PhraseStructure.Tree
