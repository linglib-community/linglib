/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain
public import Mathlib.Data.List.Dedup

/-!
# Spell-out of linearized syntactic objects

PF pronounces the pronounced copies of a linearized syntactic object (`Copy/Chain.lean`), left to
right, and nothing else, so a deleted copy, a trace, is silent wherever it stands. A token two
mothers share is one token, pronounced once, at its last occurrence, so that material two
conjuncts share is pronounced in the second. An [E] feature on a head silences the head's
complement, and since a shared token is one token, eliding either of its occurrences silences it
everywhere.

## Main definitions

* `eHeads`, `elidedDomains`, `IsSilenced`: the [E] heads, the complements they elide, one per
  term, and the tokens they silence.
* `tokens`, `pfYield`, `pfPhon`: the tokens, and the pronounced tokens and forms, left to right.
* `SpellsOut`: recognition by checked witness, an object over a lexicon pronouncing a given word
  sequence.
* `pfYieldEliding`, `AppliesVacuously`, `PronunciationEconomy`: spell-out under a given set of
  elided domains, and the ban on ellipsis that leaves pronunciation unchanged.

## Main statements

* `mem_pfYield`: a token is pronounced exactly when it has a pronounced copy and is not silenced.
* `nodup_pfYield`: a token is pronounced once at most, however many mothers dominate it.
* `isSilenced_iff_exists_mem_elidedDomains`: ellipsis counted once per elided term silences the
  same tokens.

## Implementation notes

* Movement leaves deleted copies (a copy object is read through its contraction), so no mother of
  a shared token dominates another, and de Vries's spell-out of remerged nodes, his (56),
  pronounces it once every mother has been traversed: at its last occurrence, the one `List.dedup`
  keeps.
* [E] tells PF to skip its complement (Merchant, p. 60). Ellipsis applies once per elided term, as
  Citko and Gračanin-Yuksek count it: once for a shared [E] head over a shared complement, their
  (38b), and twice over two complements, their (38d).
* Pronunciation Economy, proposed by Citko and Gračanin-Yuksek in 2020 (p. 22) and named in 2025
  (39), compares an application with all the others: neither paper orders the applications
  ("deleting one TP (say TP1)"), so the earlier ones are not singled out.

## References

* [wilder-1999]
* [de-vries-2009]
* [merchant-2001]
* [citko-gracanin-yuksek-2020]
* [citko-gracanin-yuksek-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order

variable (t : LinearizedSyntacticObject)

/-! ### Ellipsis -/

/-- The [E] heads. -/
def eHeads : List TreePath := occurrencesWith t (·.item.ellipsis)

/-- The complements of the [E] heads, one per elided term, the last of its positions. -/
def elidedDomains : List TreePath :=
  ((eHeads t).map complement).pwFilter
    fun p q ↦ subtreeAt t.val p.toList ≠ subtreeAt t.val q.toList

/-- `tok` is silenced when one of its occurrences lies in the complement of an [E] head. -/
def IsSilenced (tok : LexicalItem.Token) : Prop :=
  ∃ h ∈ eHeads t, ∃ p ∈ occurrences t tok, complement h ≤ p

instance (tok : LexicalItem.Token) : Decidable (IsSilenced t tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Ellipsis silences the same tokens whether a shared [E] head over a shared complement applies
once or at each of its occurrences. -/
theorem isSilenced_iff_exists_mem_elidedDomains {tok : LexicalItem.Token} :
    IsSilenced t tok ↔ ∃ K ∈ elidedDomains t, ∃ p ∈ occurrences t tok, K ≤ p := by
  refine ⟨fun ⟨h, hh, p, hp, ⟨q, hq⟩⟩ ↦ ?_, fun ⟨K, hK, hp⟩ ↦ ?_⟩
  · obtain ⟨K, hK, hKh⟩ : ∃ K ∈ elidedDomains t,
        subtreeAt t.val (complement h).toList = subtreeAt t.val K.toList := by
      by_contra! hne
      refine (List.forall_mem_pwFilter (fun hxz ↦ ?_) _ _).1 hne _ (List.mem_map_of_mem hh) rfl
      exact Decidable.or_iff_not_imp_left.2 fun hxy hyz ↦ hxz ((not_not.1 hxy).trans hyz)
    refine ⟨K, hK, ⟨K.toList ++ q⟩, ?_, ⟨q, rfl⟩⟩
    rw [mem_occurrences, tokenList, mem_positions_iff] at hp ⊢
    rwa [subtreeAt_append, ← hKh, ← subtreeAt_append, hq]
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.1 (List.pwFilter_subset _ hK)
    exact ⟨h, hh, hp⟩

/-! ### Pronunciation -/

/-- The tokens with a pronounced copy, left to right, each once, at its last occurrence. -/
def tokens : List LexicalItem.Token := ((tokenList t.val).map Prod.snd).dedup

/-- The pronounced tokens, left to right, each at its last occurrence unless silenced. -/
def pfYield : List LexicalItem.Token := (tokens t).filter (¬ IsSilenced t ·)

/-- The pronounced forms, left to right. -/
def pfPhon : List String := (pfYield t).filterMap (·.item.phonForm?)

/-- `t` spells `ws` from `lex`: every pronounced token's item is drawn from `lex`, and the
pronounced forms are exactly `ws`. Recognition by checked witness: a study exhibits a linearized
object over its lexicon and proves that it pronounces a row's sentence. -/
def SpellsOut (lex : List LexicalItem) (ws : List String) : Prop :=
  (∀ tok ∈ pfYield t, tok.item ∈ lex) ∧ pfPhon t = ws

instance (lex : List LexicalItem) (ws : List String) : Decidable (SpellsOut t lex ws) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem mem_pfYield {tok : LexicalItem.Token} :
    tok ∈ pfYield t ↔ (∃ p, (p, tok) ∈ tokenList t.val) ∧ ¬ IsSilenced t tok := by
  simp [pfYield, tokens, List.mem_dedup]

/-- A token is pronounced once at most, however many mothers dominate it. -/
theorem nodup_pfYield : (pfYield t).Nodup := (List.nodup_dedup _).filter _

theorem pfYield_sublist : (pfYield t).Sublist ((tokenList t.val).map Prod.snd) :=
  List.filter_sublist.trans (List.dedup_sublist _)

/-! ### Pronunciation Economy -/

/-- The pronounced tokens when ellipsis applies at the domains `Ks` alone. -/
def pfYieldEliding (Ks : List TreePath) : List LexicalItem.Token :=
  (tokens t).filter fun tok ↦ ¬ ∃ K ∈ Ks, ∃ p ∈ occurrences t tok, K ≤ p

theorem pfYieldEliding_elidedDomains : pfYieldEliding t (elidedDomains t) = pfYield t :=
  List.filter_congr fun _ _ ↦
    decide_eq_decide.2 (not_congr (isSilenced_iff_exists_mem_elidedDomains t)).symm

/-- Ellipsis applies vacuously at `K` when the other applications alone pronounce the same forms. -/
def AppliesVacuously (K : TreePath) : Prop :=
  (pfYieldEliding t ((elidedDomains t).erase K)).filterMap (·.item.phonForm?) = pfPhon t

instance (K : TreePath) : Decidable (AppliesVacuously t K) :=
  inferInstanceAs (Decidable (_ = _))

/-- Pronunciation Economy: ellipsis applies only where it has an effect on pronunciation. -/
def PronunciationEconomy : Prop := ∀ K ∈ elidedDomains t, ¬ AppliesVacuously t K

instance : Decidable (PronunciationEconomy t) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

end Minimalist
