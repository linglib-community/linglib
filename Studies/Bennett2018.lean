module

public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Prosody.Match

/-!
# Bennett 2018: recursive prosodic words in Kaqchikel

Kaqchikel prefixes fall into two prosodic classes: a low-attaching prefix is parsed into the
prosodic word of its stem, and a high-attaching prefix outside it. An onsetless syllable at the
left edge of an ω receives epenthetic [ʔ], and the OCP that fuses adjacent identical consonants is
inert across an ω boundary, so under the recursive parse [every stacked high prefix is a locus of
[ʔ]-insertion](##omegaInitial_nested) and [is separated from what follows by an ω
boundary](##mem_omegaBoundaries_nested), where the flat parse has [one
locus](##omegaInitial_flat) and [no internal boundary](##omegaBoundaries_flat). A parse of the
same bracketing without recursion [needs a different category for every
bracket](##nodup_level_of_noLevelRecursion). The recursion follows from a subcategorization frame
on the high prefixes, which [no candidate satisfies without an ω that matches no morphological
word](##prosodySyntaxMatch_pos_of_subCat), so the frame is ranked above Match (ω, X⁰).

## Implementation notes

* Every morpheme is one syllable terminal, so `flat n` also stands for the parse of high prefixes
  as syllables of their stem's ω, which differs from the low-prefix parse below the syllable.
* `matchWord` is Match (X⁰, ω) as the paper words it, a word within one ω, which asks no more
  than `Prosody.syntaxProsodyMatch`, a word coextensive with an ω.
* The hierarchy of `Prosody.Level` has no Clitic Group, so `phrasal` puts a φ in its place.

## References

* [bennett-2018]
* [selkirk-2011]: the Match constraints.
* [inkelas-1990]: prosodic subcategorization.
* [nespor-vogel-1986]: the Strict Layer Hypothesis and the Clitic Group.
-/

@[expose] public section

namespace Bennett2018

open Prosody OptimalityTheory RoseTree Core.Order

/-! ### Parses -/

/-- (4a): the flat parse `[ω Pref₁ … Prefₙ Stem]` of `n` low-attaching prefixes. -/
def flat (n : ℕ) : Tree := .om (List.replicate (n + 1) Tree.σ)

/-- (24): the bracketing `[κ₁ Pref₁ [κ₂ … [κₙ Prefₙ [ω Stem]]]]`, the stem an ω and the bracket
that each prefix opens of the category given for it. -/
def brackets (κs : List Constituent) : Tree :=
  κs.foldr (fun κ t ↦ .node κ [Tree.σ, t]) (Tree.om [Tree.σ])

/-- (23): the recursive parse `[ω Pref₁ [ω … [ω Prefₙ [ω Stem]]]]` of `n` high-attaching
prefixes, every bracket an ω. -/
def nested (n : ℕ) : Tree := brackets (.replicate n .om)

/-- (25a): a high-attaching prefix as an ω of its own beside the ω of its stem. -/
def phrasal : Tree := .ph [.om [.σ], .om [.σ]]

@[simp] theorem brackets_nil : brackets [] = Tree.om [Tree.σ] := rfl

@[simp] theorem brackets_cons (κ : Constituent) (κs : List Constituent) :
    brackets (κ :: κs) = .node κ [Tree.σ, brackets κs] := rfl

@[simp] theorem nested_zero : nested 0 = Tree.om [Tree.σ] := rfl

@[simp] theorem nested_succ (n : ℕ) : nested (n + 1) = Tree.om [Tree.σ, nested n] := rfl

@[simp] theorem numLeaves_nested (n : ℕ) : (nested n).numLeaves = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, Nat.add_comm]

theorem levelSpans_om_nested (n : ℕ) :
    (levelSpans .om (nested n)).map (·.toProd) = (List.range (n + 1)).map (·, n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : levelSpans .om (nested (n + 1)) = ⟨(0, n + 2), Nat.zero_le _⟩ ::
        (levelSpans .om (nested n)).map (.map (shift 1)) := by
      simp [levelSpans, Tree.om, Tree.σ]
      omega
    rw [h, List.range_succ_eq_map, List.map_cons, List.map_map,
      show List.map ((·.toProd) ∘ NonemptyInterval.map (shift 1)) (levelSpans .om (nested n)) =
        ((levelSpans .om (nested n)).map (·.toProd)).map (Prod.map (shift 1) (shift 1)) from
        by rw [List.map_map]; rfl, ih]
    simp [Function.comp_def, Nat.add_comm]
    omega

theorem levelSpans_om_flat (n : ℕ) :
    levelSpans .om (flat n) = [⟨(0, n + 1), Nat.zero_le _⟩] := by
  simp [levelSpans, flat, Tree.om, Tree.σ, spansList_replicate]

/-! ### The two diagnostics -/

/-- The terminals at which an ω begins. The ω is the domain of syllabification, so these are
where an onsetless syllable receives epenthetic [ʔ]. -/
def omegaInitial (t : Tree) : List ℕ := (levelSpans .om t).map (·.fst)

/-- The cuts of the frontier at which an ω begins or ends: the ω boundaries, across which
`OCP(X)ω` (18) does not see adjacent identical segments. -/
def omegaBoundaries (t : Tree) : List ℕ := (levelSpans .om t).flatMap fun s ↦ [s.fst, s.snd]

/-- Under the recursive parse each of `n` high prefixes begins an ω, as the stem does: `n + 1`
loci of [ʔ]-insertion. -/
theorem omegaInitial_nested (n : ℕ) : omegaInitial (nested n) = List.range (n + 1) := by
  simpa [omegaInitial, Function.comp_def] using
    congrArg (List.map Prod.fst) (levelSpans_om_nested n)

-- (6)–(8): under the flat parse only the first terminal begins an ω, one locus of [ʔ]-insertion.
theorem omegaInitial_flat (n : ℕ) : omegaInitial (flat n) = [0] := by
  simp [omegaInitial, levelSpans_om_flat]

-- (16)–(17): an ω boundary follows every high prefix, so no juncture degeminates.
theorem mem_omegaBoundaries_nested {n i : ℕ} : i ∈ omegaBoundaries (nested n) ↔ i ≤ n + 1 := by
  have h : omegaBoundaries (nested n) =
      ((levelSpans .om (nested n)).map (·.toProd)).flatMap fun x ↦ [x.1, x.2] := by
    simp [omegaBoundaries, List.flatMap_map]
  simp only [h, levelSpans_om_nested, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, hi⟩
    simp at hi
    omega
  · rcases h.eq_or_lt with rfl | h
    · exact ⟨(0, n + 1), ⟨0, by omega, rfl⟩, by simp⟩
    · exact ⟨(i, n + 1), ⟨i, h, rfl⟩, by simp⟩

-- (15), (29): no ω boundary falls inside the flat parse, so its junctures degeminate.
theorem omegaBoundaries_flat (n : ℕ) : omegaBoundaries (flat n) = [0, n + 1] := by
  simp [omegaBoundaries, levelSpans_om_flat]

/-! ### Without recursion -/

private theorem getElem?_level_brackets (κs : List Constituent) (i : ℕ) :
    (κs.map Constituent.level ++ [Level.om])[i]? =
      (brackets κs)[List.replicate i 1]?.map (·.value.level) := by
  induction κs generalizing i with
  | nil => cases i <;> simp [Tree.om, List.replicate_succ]
  | cons κ κs ih => cases i <;> simp [List.replicate_succ, ih]

/-- A parse of the bracketing of stacked high prefixes that repeats no category along dominance
gives every bracket a category of its own, none of them ω: the four brackets of three stacked
prefixes take four categories (24). -/
theorem nodup_level_of_noLevelRecursion {κs : List Constituent}
    (h : ∀ ℓ, NoLevelRecursion ℓ (brackets κs)) :
    (κs.map Constituent.level ++ [Level.om]).Nodup := by
  refine List.nodup_iff_getElem?_ne_getElem?.2 fun i j hij hj heq ↦ ?_
  have hℓ := List.getElem?_eq_getElem hj
  rw [hℓ, getElem?_level_brackets] at heq
  rw [getElem?_level_brackets] at hℓ
  obtain ⟨s, hs, hsℓ⟩ := Option.map_eq_some_iff.1 heq
  obtain ⟨u, hu, huℓ⟩ := Option.map_eq_some_iff.1 hℓ
  have hle : (⟨.replicate i 1⟩ : TreePath) ≤ ⟨.replicate j 1⟩ :=
    ⟨.replicate (j - i) 1, by rw [List.replicate_append_replicate]; congr 1; omega⟩
  have := congrArg (·.toList.length) <| (h _).subsingleton_inter_Iic ⟨.replicate j 1⟩
    ⟨⟨s, hs, hsℓ⟩, Set.mem_Iic.2 hle⟩ ⟨⟨u, hu, huℓ⟩, Set.mem_Iic.2 le_rfl⟩
  simp at this
  omega

-- A φ over the stem's ω repeats no category, and a second φ over it does.
example : ∀ ℓ, NoLevelRecursion ℓ (brackets [.ph]) := fun ℓ ↦ by cases ℓ <;> decide
example : ¬ NoLevelRecursion .ph (brackets [.ph, .ph]) := by decide

-- The recursive parse repeats ω along dominance.
example (n : ℕ) : ¬ ∀ ℓ, NoLevelRecursion ℓ (nested (n + 1)) := fun h ↦ by
  simpa [List.replicate_succ] using
    nodup_level_of_noLevelRecursion (κs := .replicate (n + 1) .om) h

/-! ### Constraints and the ranking -/

/-- The morphological word of `n` prefixes and a stem, in syllables. -/
abbrev word (n : ℕ) : NonemptyInterval ℕ := ⟨(0, n + 1), Nat.zero_le _⟩

/-- (13): Match (X⁰, ω), one violation for each morphological word whose segments are not all
within one ω. -/
def matchWord (α : List (NonemptyInterval ℕ)) : Constraint Tree :=
  (Constraint.align (· ≤ ·)).comap fun t ↦ (α, levelSpans .om t)

/-- (30): the subcategorization frame `[ω HighPref [ω ]]`, an ω whose daughters are a syllable
and an ω. -/
@[mk_iff]
structure IsFrame (t : Tree) : Prop where
  /-- The frame is an ω. -/
  level : t.value.level = .om
  /-- Its daughters are the prefix syllable and the ω of the stem. -/
  daughters : t.children.map (·.value.level) = [.syl, .om]

instance : DecidablePred IsFrame := fun _ ↦ decidable_of_iff' _ (isFrame_iff _)

/-- `SubCat`: one violation for each high-attaching prefix, given by its index in the frontier,
at which no frame (30) begins. -/
def subCat (prefs : List ℕ) : Constraint Tree :=
  (Constraint.align fun (i : ℕ) (s : NonemptyInterval ℕ) ↦ i = s.fst).comap fun t ↦
    (prefs, t.spans IsFrame)

/-- A candidate that gives a high prefix its frame has an ω that matches no morphological word,
whatever the word: `SubCat` and Match (ω, X⁰) conflict in every candidate. -/
theorem prosodySyntaxMatch_pos_of_subCat {t : Tree} {i m : ℕ} (h : subCat [i] t = 0) :
    0 < prosodySyntaxMatch .om [⟨(0, m), Nat.zero_le m⟩] t := by
  obtain ⟨_, hx, rfl⟩ : ∃ x ∈ t.spans IsFrame, i = x.fst := by
    simpa using Constraint.align_eq_zero_iff.1 h
  obtain ⟨p, ⟨κ, cs⟩, hs, ⟨-, hcs⟩, rfl⟩ := mem_spans.1 hx
  obtain ⟨a, b, rfl, -, hb⟩ : ∃ a b, cs = [a, b] ∧ a.value.level = .syl ∧ b.value.level = .om := by
    simpa [List.map_eq_cons_iff] using hcs
  refine List.countP_pos_iff.2 ⟨t.spanAt (p ++ [1]) b,
    mem_spans.2 ⟨p ++ [1], b, by simp [getElem?_append, hs], hb, rfl⟩, ?_⟩
  have := a.numLeaves_pos
  simp [NonemptyInterval.ext_iff, spanAt, leafIndex_append hs, leafIndex_cons]
  rintro _ h₁ h₂
  have := congrArg Prod.fst (h₂.trans h₁)
  simp at this
  omega

/-- A high-attaching prefix is parsed recursively: under `SubCat ≫ Match (ω, X⁰)`, with
Match (X⁰, ω) undominated, the recursive parse is the unique optimum. -/
theorem high_prefix_recursive :
    (Tableau.ofList {nested 1, flat 1, phrasal}
      [matchWord [word 1], subCat [0], prosodySyntaxMatch .om [word 1]]).optimal = {nested 1} := by
  decide

/-- A low-attaching prefix, carrying no frame, is parsed flat: Match (ω, X⁰) alone rules out the
extra ω. -/
theorem low_prefix_flat :
    (Tableau.ofList {nested 1, flat 1, phrasal}
      [matchWord [word 1], prosodySyntaxMatch .om [word 1]]).optimal = {flat 1} := by
  decide

-- (22): three stacked high prefixes each realise their frame only in the recursive parse, at the
-- cost of three ω's that match no word.
example : subCat [0, 1, 2] (nested 3) = 0 := by decide
example : subCat [0, 1, 2] (flat 3) = 3 := by decide
example : prosodySyntaxMatch .om [word 3] (nested 3) = 3 := by decide
example : prosodySyntaxMatch .om [word 3] (flat 3) = 0 := by decide

-- A word coextensive with an ω is within one, and a word inside a larger ω is within it
-- without being coextensive with it.
example (α : List (NonemptyInterval ℕ)) (t : Tree) :
    matchWord α t ≤ syntaxProsodyMatch α .om t := by
  refine List.countP_mono_left fun m _ h ↦ ?_
  simp only [decide_eq_true_eq] at h ⊢
  exact fun w hw hmw ↦ h w hw hmw.le

example : matchWord [word 0] (flat 1) = 0 := by decide
example : syntaxProsodyMatch [word 0] .om (flat 1) = 1 := by decide

-- The recursive optimum is a well-formed prosodic word: ω over ω is admitted by Layeredness;
-- only the violable Match (ω, X⁰) penalises it.
example : IsWord (nested 1) := by decide

end Bennett2018
