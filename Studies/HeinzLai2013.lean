/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Linglib.Data.Wordlist.HeinzLai2013
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Phonology.Subregular.WeakDeterminism

/-!
# Heinz and Lai (2013): Vowel harmony and subsequentiality

Heinz and Lai place iterative vowel harmony in the subsequential hierarchy. Over the alphabet of
§3, harmonizing vowels `+` and `−`, an inert class `C` of consonants and transparent vowels, and
opaque vowels `⊞` and `⊟`, progressive harmony is computed left to right by the sequential
transducer of Figure 2, and regressive harmony by the same transducer run right to left. Sour
grapes harmony (8) is not left-subsequential (Theorem 5), and dominant–recessive harmony (9) is
subsequential in neither direction (Theorem 6), but it is weakly deterministic in the sense of
their Definition 1 (Theorem 7): progressive spreading of `+` alone, Figure 4, run left to right
and then right to left.

## Main definitions

* `Seg`: the alphabet of §3
* `ph`: progressive harmony, the transducer of Figure 2
* `IsSourGrapes`, `IsDominantRecessive`: the conditions (8) and (9)
* `php`: progressive spreading of `+` alone, the transducer of Figure 4

## Implementation notes

* The proof of Theorem 5 goes through the bounded delay of left-subsequential functions rather
  than the paper's sets of tails.
* Theorem 7 is stated, as in the paper, for words over `+` and `−`.
* Not formalized: Theorem 4 (majority rules is not regular) and the stem-control results
  (Theorems 8 and 9).

## Errata

* Theorem 5 also claims that no length-preserving map meeting (8) is right-subsequential, by an
  argument omitted as similar. Condition (8) fixes the map only on words that begin with `+`, and
  the right-to-left pass that raises every `−` unless the word ends in `⊟` meets it and
  [is right-subsequential](##exists_isRightSubsequential_isSourGrapes). The right half
  [holds](##not_isRightSubsequential_of_isSourGrapes) once the map also leaves every trigger-free
  word `−ⁿ` unchanged: the last `−` of `+−ⁿ` then surfaces `+` and that of `−−ⁿ` does not, a
  difference made `n` positions away.
* The paper conjectures that sour grapes harmony is not weakly deterministic. For the maps
  meeting (8) the conjecture fails: the same right-to-left pass preserves length, so it is
  [weakly deterministic](##exists_isWeaklyDeterministic_isSourGrapes) after the identity.

## References

* [heinz-lai-2013]
-/

@[expose] public section

namespace HeinzLai2013

open List

/-- A symbol of the alphabet of §3 is a harmonizing vowel `+` or `−`, the inert class `C`, or an
opaque vowel `⊞` or `⊟`. -/
inductive Seg
  | plus
  | minus
  | inert
  | opaquePlus
  | opaqueMinus
  deriving DecidableEq, Repr

/-! ### Progressive harmony -/

/-- Progressive harmony, Figure 2. The state is the value of the current harmonic domain, set by
the first harmonizing vowel and reset by each opaque vowel; a harmonizing vowel takes that
value. Run right to left, the same machine computes regressive harmony. -/
def ph : Mealy (Option Bool) Seg Seg where
  start := none
  step b a := match a with
    | .plus => some (b.getD true)
    | .minus => some (b.getD false)
    | .opaquePlus => some true
    | .opaqueMinus => some false
    | .inert => b
  output b a := match a, b with
    | .plus, some false => .minus
    | .minus, some true => .plus
    | a, _ => a

/-- `ofLetter c` is the class of the Turkish letter `c`. The vowels `i` and `e` are `[−back]`,
`o` and `u` are `[+back]`, and everything else is inert. -/
def ofLetter : Char → Seg
  | 'i' | 'e' => .minus
  | 'o' | 'u' => .plus
  | _ => .inert

/-- `ofAnalysis a` is the underlying and the surface string of the word `a` analyses, read off
its underlying form without the slashes and the morpheme boundary, and off its segments. -/
def ofAnalysis (a : Wordlist.Analysis) : List Seg × List Seg :=
  ((a.underlying.toList.filter fun c ↦ c != '/' && c != '-').map ofLetter,
    a.form.segments.map fun s ↦ (s.toList.headD ' ' |> ofLetter))

-- Table 2
theorem ph_forms : ∀ a ∈ Wordlist.analyses, ph.run (ofAnalysis a).1 = (ofAnalysis a).2 := by
  decide

/-! ### Sour grapes -/

/-- `f` meets the sour-grapes condition (8). A trigger followed by `−`s spreads to all of them, and
does not spread at all when an opaque `⊟` ends the word. -/
def IsSourGrapes (f : List Seg → List Seg) : Prop :=
  ∀ n, f (.plus :: replicate n .minus) = replicate (n + 1) .plus ∧
    f (.plus :: replicate n .minus ++ [.opaqueMinus]) =
      .plus :: replicate n .minus ++ [.opaqueMinus]

/-- No left-subsequential function meets (8) (Theorem 5). -/
theorem not_isLeftSubsequential_of_isSourGrapes {f : List Seg → List Seg} (hf : IsSourGrapes f) :
    ¬ IsLeftSubsequential f :=
  not_isLeftSubsequential_of_diverging fun N ↦
    ⟨.plus :: replicate (N + 1) .minus, [.opaqueMinus], 1, by
      rw [(hf (N + 1)).1]; simp; omega, by
      rw [(hf (N + 1)).1, cons_append, ← cons_append, (hf (N + 1)).2]; simp⟩

/-- The right-to-left pass that raises every `−` unless the word ends in `⊟`. Its state records,
after the first symbol read, whether that symbol was `⊟`. -/
def raiseUnlessFinalBlocked : Mealy (Option Bool) Seg Seg where
  start := none
  step b a := some (b.getD (a == .opaqueMinus))
  output b a := if a = .minus ∧ b ≠ some true then .plus else a

private theorem raiseUnlessFinalBlocked_runFrom_false (n : ℕ) :
    raiseUnlessFinalBlocked.runFrom (some false) (replicate n .minus ++ [.plus]) =
      replicate (n + 1) .plus := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ, cons_append, Mealy.runFrom_cons]
    exact congrArg (List.cons _) ih

private theorem raiseUnlessFinalBlocked_runFrom_true (xs : List Seg) :
    raiseUnlessFinalBlocked.runFrom (some true) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Mealy.runFrom_cons]
    exact congr (congrArg List.cons (by simp [raiseUnlessFinalBlocked])) ih

private theorem raiseUnlessFinalBlocked_run (n : ℕ) :
    raiseUnlessFinalBlocked.run (replicate n .minus ++ [.plus]) = replicate (n + 1) .plus := by
  rcases n with _ | n
  · rfl
  · rw [replicate_succ, cons_append, Mealy.run, Mealy.runFrom_cons,
      show raiseUnlessFinalBlocked.step raiseUnlessFinalBlocked.start Seg.minus = some false
        from rfl,
      raiseUnlessFinalBlocked_runFrom_false]
    rfl

private theorem isSourGrapes_raiseUnlessFinalBlocked :
    IsSourGrapes raiseUnlessFinalBlocked.runRight := by
  refine fun n ↦ ⟨?_, ?_⟩
  · rw [Mealy.runRight, reverse_cons, reverse_replicate, raiseUnlessFinalBlocked_run,
      reverse_replicate]
  · have : (Seg.plus :: replicate n Seg.minus ++ [Seg.opaqueMinus]).reverse =
        Seg.opaqueMinus :: (replicate n Seg.minus ++ [Seg.plus]) := by simp
    rw [Mealy.runRight, this, Mealy.run, Mealy.runFrom_cons,
      show raiseUnlessFinalBlocked.step raiseUnlessFinalBlocked.start Seg.opaqueMinus = some true
        from rfl, raiseUnlessFinalBlocked_runFrom_true]
    simp [raiseUnlessFinalBlocked]

-- Theorem 5, right half
theorem exists_isRightSubsequential_isSourGrapes :
    ∃ f : List Seg → List Seg, IsSourGrapes f ∧ IsRightSubsequential f :=
  ⟨_, isSourGrapes_raiseUnlessFinalBlocked, raiseUnlessFinalBlocked.isRightSubsequential⟩

/-- A length-preserving map meeting (8) is weakly deterministic, against the paper's conjecture
for sour grapes harmony. -/
theorem exists_isWeaklyDeterministic_isSourGrapes :
    ∃ f : List Seg → List Seg,
      (∀ w, (f w).length = w.length) ∧ IsSourGrapes f ∧ IsWeaklyDeterministic f :=
  ⟨_, fun _ ↦ Mealy.length_runRight .., isSourGrapes_raiseUnlessFinalBlocked,
    raiseUnlessFinalBlocked.isRightSubsequential.isWeaklyDeterministic⟩

/-- No length-preserving right-subsequential function meets (8) and leaves every trigger-free `−ⁿ`
unchanged, the right half of Theorem 5 with the hypothesis on `−ⁿ` it needs. -/
theorem not_isRightSubsequential_of_isSourGrapes {f : List Seg → List Seg}
    (hlen : ∀ w, (f w).length = w.length) (hf : IsSourGrapes f)
    (hnone : ∀ n, f (replicate n .minus) = replicate n .minus) : ¬ IsRightSubsequential f := by
  intro hR
  obtain ⟨N, hN⟩ := hR.boundedDependence_left hlen
  have h : (f (.plus :: replicate (N + 1) .minus))[N + 1]?
      = (f (.minus :: replicate (N + 1) .minus))[N + 1]? := hN (N + 1) (by simp)
  rw [(hf (N + 1)).1, ← replicate_succ, hnone] at h
  simp at h

/-! ### Dominant–recessive harmony -/

/-- `f` meets the dominant–recessive condition (9). On words over `+` and `−`, every vowel surfaces
`+` if some vowel is `+`, and `−` otherwise. -/
def IsDominantRecessive (f : List Seg → List Seg) : Prop :=
  ∀ w, (∀ a ∈ w, a = .plus ∨ a = .minus) →
    f w = if .plus ∈ w then replicate w.length .plus else replicate w.length .minus

/-- No length-preserving subsequential function, in either direction, meets (9) (Theorem 6). -/
theorem not_isSubsequential_of_isDominantRecessive {f : List Seg → List Seg}
    (hlen : ∀ w, (f w).length = w.length) (hf : IsDominantRecessive f) :
    ∀ d, ¬ IsSubsequential d f := by
  refine TwoSidedUnboundedDependence.not_isSubsequential ?_ hlen
  have hw : ∀ x y : Seg, (x = .plus ∨ x = .minus) → (y = .plus ∨ y = .minus) → ∀ n,
      ∀ a ∈ flankWord x .minus y n, a = .plus ∨ a = .minus := fun x y hx hy n a ha ↦ by
    simp only [flankWord, mem_cons, mem_append, mem_replicate, not_mem_nil, or_false] at ha
    rcases ha with rfl | ⟨-, rfl⟩ | rfl <;> simp_all
  refine .of_flanks (fill := .minus) (xOn := .minus) (yOn := .minus) (xOff := .plus)
    (yOff := .plus) (n := fun d ↦ 2 * d + 1) (t := fun d ↦ d + 1) (fun _ ↦ by omega)
    (fun _ ↦ by omega) (fun d ↦ ?_) (fun d ↦ ?_) <;>
  · rw [hf _ (hw _ _ (by simp) (by simp) _), hf _ (hw _ _ (by simp) (by simp) _)]
    simp [flankWord, mem_replicate, show d + 1 < 2 * d + 1 + 1 + 1 by omega]

/-- Progressive spreading of `+` alone (Figure 4) turns every `−` after a `+` into `+`. -/
def php : Mealy Bool Seg Seg :=
  .ofFlag (· == .plus) fun l a ↦ if l && a == .minus then .plus else a

/-- A word over `+` and `−`. -/
private def PlusMinus (w : List Seg) : Prop := ∀ a ∈ w, a = .plus ∨ a = .minus

private theorem php_runFrom_true {xs : List Seg} (hxs : PlusMinus xs) :
    php.runFrom true xs = replicate xs.length .plus := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Mealy.runFrom_cons, length_cons, replicate_succ]
    have hx := hxs x mem_cons_self
    rcases hx with rfl | rfl <;>
      exact congrArg₂ List.cons rfl (ih fun a ha ↦ hxs a (mem_cons_of_mem _ ha))

private theorem php_runFrom_false_replicate (k : ℕ) :
    php.runFrom false (replicate k .minus) = replicate k .minus := by
  induction k with
  | zero => rfl
  | succ k ih => rw [replicate_succ, Mealy.runFrom_cons]; exact congrArg (List.cons _) ih

private theorem php_run_split (k : ℕ) {rest : List Seg} (hrest : PlusMinus rest) :
    php.run (replicate k .minus ++ .plus :: rest) =
      replicate k .minus ++ replicate (rest.length + 1) .plus := by
  rw [Mealy.run, Mealy.runFrom_append, show php.start = false from rfl,
    php_runFrom_false_replicate, show php.evalFrom false (replicate k .minus) = false by
      simp [php], Mealy.runFrom_cons, show php.step false Seg.plus = true from rfl,
    php_runFrom_true hrest]
  rfl

private theorem exists_split {w : List Seg} (hw : PlusMinus w) (h : .plus ∈ w) :
    ∃ k rest, w = replicate k .minus ++ .plus :: rest := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    rcases hw a mem_cons_self with rfl | rfl
    · exact ⟨0, w, rfl⟩
    · obtain ⟨k, rest, rfl⟩ := ih (fun b hb ↦ hw b (mem_cons_of_mem _ hb)) (by simpa using h)
      exact ⟨k + 1, rest, rfl⟩

private theorem eq_replicate_minus {w : List Seg} (hw : PlusMinus w) (h : .plus ∉ w) :
    w = replicate w.length .minus :=
  eq_replicate_iff.mpr ⟨rfl, fun a ha ↦ (hw a ha).resolve_left fun hp ↦ h (hp ▸ ha)⟩

-- Theorem 7
theorem isDominantRecessive_php : IsDominantRecessive (php.runRight ∘ php.run) := by
  intro w hw
  by_cases h : .plus ∈ w
  · obtain ⟨k, rest, rfl⟩ := exists_split hw h
    have hrest : PlusMinus rest := fun a ha ↦ hw a (by simp [ha])
    simp only [h, ↓reduceIte, Function.comp_apply]
    rw [php_run_split k hrest, Mealy.runRight]
    have hrev : (replicate k Seg.minus ++ replicate (rest.length + 1) Seg.plus).reverse =
        Seg.plus :: (replicate rest.length Seg.plus ++ replicate k Seg.minus) := by
      simp [replicate_succ']
    have hpm : PlusMinus (replicate rest.length Seg.plus ++ replicate k Seg.minus) := fun a ha ↦ by
      simp only [mem_append, mem_replicate] at ha
      rcases ha with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    rw [hrev, Mealy.run, Mealy.runFrom_cons, show php.step php.start Seg.plus = true from rfl,
      php_runFrom_true hpm, show php.output php.start Seg.plus = Seg.plus from rfl,
      ← replicate_succ, reverse_replicate]
    simp
    omega
  · simp only [h, ↓reduceIte, Function.comp_apply]
    rw [eq_replicate_minus hw h, length_replicate, Mealy.runRight, Mealy.run,
      show php.start = false from rfl, php_runFrom_false_replicate, reverse_replicate,
      php_runFrom_false_replicate, reverse_replicate]

/-- Dominant–recessive harmony is weakly deterministic (Theorem 7). -/
theorem isWeaklyDeterministic_php : IsWeaklyDeterministic (php.runRight ∘ php.run) :=
  ⟨php.run, php.runRight, php.isLeftSubsequential, fun _ ↦ (php.length_run _).le,
    php.isRightSubsequential, rfl⟩

end HeinzLai2013
