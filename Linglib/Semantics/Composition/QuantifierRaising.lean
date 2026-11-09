module

public import Linglib.Syntax.Tree.QuantifierRaising
public import Linglib.Semantics.Composition.Tree

/-!
# The interpretation of Quantifier Raising

A raised constituent combines with the abstract over its trace. When the trace has the
constituent's own type, the abstract applied to the constituent's value is the value of the tree
before raising, so [raising is β-expansion and changes
nothing](##PhraseStructure.Tree.realize_raise);
a constituent takes scope only when its trace is of another type, as a quantifier's trace is an
individual. The theorem rests on [the value of a tree with a trace for a
constituent](##PhraseStructure.Tree.realize_replaceAt_trace), and holds in the interpretations
where applying an abstraction is substitution, the total one among them.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

open Montague

namespace PhraseStructure.Tree

section Semantics

universe u v w

variable {C : Type} {K : Ty → Type u} {L : Type*} (A : Interpretation.{u, v, w} K) (Γ : ℕ → Ty)
  (lex : L → Option (Σ ty, K ty))

/-- Putting a trace for a constituent, and assigning the trace's index the constituent's value,
leaves the value of the tree unchanged, provided the index is new and no binder above the
constituent has it or binds into the constituent. -/
theorem realize_replaceAt_trace {a : Tree C L} {n : ℕ} (c : C) {v : A.Val (Γ n)} :
    ∀ {p : List ℕ} {t : Tree C L} {g : ∀ k, A.Val (Γ k)}, t[p]? = some a → n ∉ t.freeIndices →
      n ∉ t.bindersAbove p → Disjoint (t.bindersAbove p) a.freeIndices →
      realize A Γ lex g a = some ⟨Γ n, A.var v⟩ →
      realize A Γ lex (Function.update g n v) (t.replaceAt p (trace n c)) = realize A Γ lex g t
  | [], t, g, h, _, _, _, ha => by
    obtain rfl : t = a := Option.some.inj h
    rw [RoseTree.replaceAt_nil, realize_trace, ha, Function.update_self]
  | i :: p, t, g, h, hn, hnb, hab, ha => by
    obtain ⟨ch, hc, hcs⟩ := RoseTree.getElem?_cons_eq_some_iff.mp h
    rw [RoseTree.replaceAt_cons_of_getElem? hc]
    obtain ⟨l, cs⟩ := t
    rw [RoseTree.children_node] at hc
    have hmem : ch ∈ cs := List.mem_of_getElem? hc
    have ih := fun (g' : ∀ k, A.Val (Γ k)) (hn' : n ∉ Tree.freeIndices ch)
        (hnb' : n ∉ Tree.bindersAbove ch p) (hab' : Disjoint (Tree.bindersAbove ch p) a.freeIndices)
        (ha' : realize A Γ lex g' a = some ⟨Γ n, A.var v⟩) ↦
      realize_replaceAt_trace c (p := p) (t := ch) (g := g') hcs hn' hnb' hab' ha'
    simp only [RoseTree.value_node, RoseTree.children_node]
    cases l with
    | terminal c' w' =>
      have hne : cs ≠ [] := List.ne_nil_of_mem hmem
      rw [realize_junk (h := by simpa [Label.Licenses] using hne),
        realize_junk (h := by simpa [Label.Licenses] using hne)]
    | trace m c' =>
      have hne : cs ≠ [] := List.ne_nil_of_mem hmem
      rw [realize_junk (h := by simpa [Label.Licenses] using hne),
        realize_junk (h := by simpa [Label.Licenses] using hne)]
    | bind m c' =>
      by_cases hlen : cs.length = 1
      · obtain ⟨body, rfl⟩ := List.length_eq_one_iff.mp hlen
        obtain ⟨rfl, rfl⟩ : i = 0 ∧ body = ch := by
          rcases i with _ | i
          · exact ⟨rfl, by simpa using hc⟩
          · simp at hc
        rw [show (RoseTree.node (.bind m c') [body] : Tree C L) = bind m c' body from rfl,
          bindersAbove_bind] at hnb hab
        have hmn : m ≠ n := fun hmn ↦ hnb (hmn ▸ Finset.mem_insert_self _ _)
        have hma : m ∉ a.freeIndices := Finset.disjoint_left.mp hab (Finset.mem_insert_self _ _)
        have hnb' : n ∉ Tree.bindersAbove body p := fun h' ↦ hnb (Finset.mem_insert_of_mem h')
        have hab' : Disjoint (Tree.bindersAbove body p) a.freeIndices :=
          hab.mono_left (Finset.subset_insert _ _)
        have hn' : n ∉ Tree.freeIndices body := fun hmem' ↦ hn (by
          rw [show (RoseTree.node (.bind m c') [body] : Tree C L) = bind m c' body from rfl,
            freeIndices_bind]
          exact Finset.mem_erase.mpr ⟨Ne.symm hmn, hmem'⟩)
        change realize A Γ lex _ (bind m c' _) = realize A Γ lex g (bind m c' body)
        rw [realize_bind, realize_bind, ih g hn' hnb' hab' ha]
        congr 1
        funext d
        congr 2
        funext x
        rw [Function.update_comm (Ne.symm hmn)]
        rw [ih (Function.update g m x) hn' hnb' hab' (by
          rw [← ha]
          exact realize_congr_of_agree A Γ lex fun j hj ↦
            Function.update_of_ne (fun hjm ↦ hma (by rw [← hjm]; exact hj)) _ _)]
      · rw [realize_junk (h := by simpa [Label.Licenses] using hlen),
          realize_junk (h := by simpa [Label.Licenses] using hlen)]
    | phrase c' k =>
      have hfree : ∀ s ∈ cs, n ∉ Tree.freeIndices s := fun s hs hmem' ↦ hn (by
        rw [show (RoseTree.node (.phrase c' k) cs : Tree C L) = phrase c' k cs from rfl]
        exact mem_freeIndices_phrase.mpr ⟨s, hs, hmem'⟩)
      have hagree : ∀ s ∈ cs, realize A Γ lex (Function.update g n v) s = realize A Γ lex g s :=
        fun s hs ↦ realize_congr_of_agree A Γ lex fun j hj ↦
          Function.update_of_ne (fun hjn ↦ hfree s hs (by rw [← hjn]; exact hj)) _ _
      rw [show (RoseTree.node (.phrase c' k) cs : Tree C L) = phrase c' k cs from rfl,
        bindersAbove_phrase hc] at hnb hab
      have ihc := ih g (hfree ch hmem) hnb hab ha
      match cs, i, hc, hagree with
      | [], _, hc, _ => simp at hc
      | [t₁], 0, hc, _ =>
        obtain rfl : t₁ = ch := by simpa using hc
        exact ihc
      | [t₁], _ + 1, hc, _ => simp at hc
      | [t₁, t₂], 0, hc, hagree =>
        obtain rfl : t₁ = ch := by simpa using hc
        change realize A Γ lex _ (phrase c' k [_, t₂]) = realize A Γ lex g (phrase c' k [t₁, t₂])
        rw [realize_phrase_binary, realize_phrase_binary, ihc, hagree t₂ (by simp)]
      | [t₁, t₂], 1, hc, hagree =>
        obtain rfl : t₂ = ch := by simpa using hc
        change realize A Γ lex _ (phrase c' k [t₁, _]) = realize A Γ lex g (phrase c' k [t₁, t₂])
        rw [realize_phrase_binary, realize_phrase_binary, ihc, hagree t₁ (by simp)]
      | [t₁, t₂], _ + 2, hc, _ => simp at hc
      | t₁ :: t₂ :: t₃ :: ts, 0, _, _ => rfl
      | t₁ :: t₂ :: t₃ :: ts, 1, _, _ => rfl
      | t₁ :: t₂ :: t₃ :: ts, 2, _, _ => rfl
      | t₁ :: t₂ :: t₃ :: ts, _ + 3, _, _ => rfl

/-- Quantifier Raising is β-expansion: in an interpretation where applying an abstraction to a
variable's value is substitution, raising a constituent whose trace has the constituent's own type
leaves the value of the tree unchanged. Scope is taken only where the two types differ. -/
theorem realize_raise
    (hβ : ∀ {σ τ : Ty} (x : A.Val σ) (f : A.Val σ → A.D τ),
      A.mode .functionalRight (A.var x) (A.lam f) = f x)
    {g : ∀ k, A.Val (Γ k)} {t a : Tree C L} {p : List ℕ} {n : ℕ}
    (h : t[p]? = some a) (hn : n ∉ t.freeIndices)
    (hnb : n ∉ t.bindersAbove p) (hab : Disjoint (t.bindersAbove p) a.freeIndices)
    {v : A.Val (Γ n)} (ha : realize A Γ lex g a = some ⟨Γ n, A.var v⟩) :
    realize A Γ lex g (t.raise n p) = realize A Γ lex g t := by
  have hsub := realize_replaceAt_trace A Γ lex (Tree.cat a) h hn hnb hab ha
  have hty := (realize_map_fst A Γ lex g (t.replaceAt p (trace n (Tree.cat a)))).trans
    (realize_map_fst A Γ lex (Function.update g n v) _).symm
  rw [raise_of_getElem? h, adjoin, realize_phrase_binary, realize_bind, ha, Option.bind_some]
  rw [hsub] at hty
  rcases hd : realize A Γ lex g t with _ | ⟨τ, d⟩
  · rw [hd, Option.map_none, Option.map_eq_none_iff] at hty
    rw [hty, Option.map_none, Option.bind_none]
  · rw [hd] at hty
    obtain ⟨⟨τ', d'⟩, hd', (rfl : τ' = τ)⟩ := Option.map_eq_some_iff.mp hty
    rw [hd', Option.map_some, Option.bind_some, Mode.combine?_fn_right, hβ, hsub, hd,
      valueAt_some]

end Semantics

section Total

variable {C : Type} {L : Type*} {E W : Type} {S : Sorts}

/-- Under the total interpretation, raising a constituent whose trace has its own type leaves the
denotation unchanged. -/
theorem interpWith_raise {Γ : ℕ → Ty} {lex : L → Option (Denotation E W Id S)}
    {g : ∀ k, Ty.Domain E W (Γ k) S} {t a : Tree C L} {p : List ℕ} {n : ℕ}
    (h : t[p]? = some a) (hn : n ∉ t.freeIndices)
    (hnb : n ∉ t.bindersAbove p) (hab : Disjoint (t.bindersAbove p) a.freeIndices)
    {v : Ty.Domain E W (Γ n) S} (ha : interpWith Γ lex g a = some ⟨Γ n, v⟩) :
    interpWith Γ lex g (t.raise n p) = interpWith Γ lex g t :=
  realize_raise _ Γ lex (fun _ _ ↦ rfl) h hn hnb hab ha

end Total

end PhraseStructure.Tree
