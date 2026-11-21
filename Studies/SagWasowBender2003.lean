module

public import Linglib.Syntax.HPSG.Binding
public import Linglib.Syntax.HPSG.Construction
public import Linglib.Data.Examples.SagWasowBender2003
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.English.Pronouns

/-!
# Sag, Wasow & Bender (2003): Syntactic Theory: A Formal Introduction

This file formalizes the binding theory of Chapter 7 and the long-distance dependencies of
Chapter 15, in the RSRL model theory of `Syntax/HPSG/RSRL`.

A reflexive must be outranked by a coindexed argument on some argument-structure list, and a
nonreflexive pronoun must not be. We model a sentence by two words with their argument
structures, and the textbook's judgments follow (`binding_rows`). Person, number and gender
belong to the index, so a reflexive is licensed with a pronoun antecedent exactly when the two
are compatible in them (`licenses_iff_compat`).

The feature `GAP` lists the missing arguments of a phrase. Conjuncts share their `GAP` lists, so
a gap in only one conjunct is rejected and a gap in every conjunct is accepted
(`coordination_rows`).

## Implementation notes

A sentence counts as grammatical when its utterance satisfies the binding principles at its
root. An RSRL model asks this of every entity; the two agree when the pronoun is on only one
argument structure (`models_utterance_iff`), as in every sentence here. The object of an
argument-marking preposition takes the place of its PP on the verb's argument structure.

The textbook keeps person, number and gender in `AGR` and adds an agreement principle; here they
are on the index, as in [pollard-sag-1994]. Coordination is binary, and the Argument Realization
Principle and the subject-extraction rule are not modelled.

## References

* [sag-wasow-bender-2003]
* [pollard-sag-1994]
* [ross-1967]
* [chomsky-1981]
-/

@[expose] public section

namespace SagWasowBender2003

open HPSG.RSRL HPSG.Construction

/-- The rows on a topic. -/
def probing (t : Examples.Topic) : List Datum :=
  Examples.all.filter fun x ↦ decide (Examples.topic x = some t)

/-! ### Binding theory -/

/-- The number values of an index. -/
inductive Num | sing | plur
  deriving DecidableEq, Fintype, Repr

/-- The gender values of an index. -/
inductive Gend | masc | fem | neut
  deriving DecidableEq, Fintype, Repr

/-- The person, number and gender values of an index. -/
structure Agr where
  /-- The person value. -/
  per : Person
  /-- The number value. -/
  num : Num
  /-- The gender value. -/
  gend : Gend
  deriving DecidableEq, Fintype, Repr

/-- The third person singular feminine, the values of the index of *Susan*. -/
def Agr.susan : Agr := ⟨.third, .sing, .fem⟩

/-- The members of the argument structures of a worked utterance: *Susan*, the pronoun, one
other nominal, and a clause. -/
inductive Syn | susan | pron | other | clause
  deriving DecidableEq, Fintype, Repr

/-- The entities of a worked utterance are its root, the list of its two words, the words, the
rests of their argument structures, the members of those, their indices, and the person, number
and gender values. -/
inductive Ent
  | root
  | dtrs (i : Fin 3)
  | word (i : Fin 2)
  | args (i : Fin 2) (j : Fin 4)
  | syn (a : Syn)
  | idx (a : Syn)
  | per (p : Person)
  | num (n : Num)
  | gend (g : Gend)
  deriving DecidableEq, Fintype, Repr

/-- The worked utterance of two words with the argument structures `args 0` and `args 1`, of at
most three members each. *Susan* and the other nominal are nonpronouns, the pronoun has the sort
`pronSort` and the index of `pronIdx`, and the indices of *Susan* and of the pronoun have the
values `subjAgr` and `objAgr`. -/
@[reducible] def utterance (args : Fin 2 → List Syn) (pronSort : Binding.Srt) (pronIdx : Syn)
    (subjAgr objAgr : Agr) : Interpretation Binding.sig Ent where
  S
    | .root => .phrase
    | .dtrs 2 => .elist
    | .dtrs _ => .nelist
    | .word _ => .word
    | .args i j => if j.val < (args i).length then .nelist else .elist
    | .syn .pron => pronSort
    | .syn .clause => .verbal
    | .syn _ => .npro
    | .idx _ => .idx
    | .per .first => .first
    | .per .second => .second
    | .per .third => .third
    | .num .sing => .sing
    | .num .plur => .plur
    | .gend .masc => .masc
    | .gend .fem => .fem
    | .gend .neut => .neut
  A
    | .DTRS, .root => some (.dtrs 0)
    | .FIRST, .dtrs 0 => some (.word 0)
    | .FIRST, .dtrs 1 => some (.word 1)
    | .REST, .dtrs 0 => some (.dtrs 1)
    | .REST, .dtrs 1 => some (.dtrs 2)
    | .ARGST, .word i => some (.args i 0)
    | .FIRST, .args i j => (args i)[j.val]?.map .syn
    | .REST, .args i j => (args i)[j.val]?.map fun _ ↦ .args i (j + 1)
    | .IDX, .syn .pron => some (.idx pronIdx)
    | .IDX, .syn .clause => none
    | .IDX, .syn a => some (.idx a)
    | .PER, .idx .susan => some (.per subjAgr.per)
    | .NUM, .idx .susan => some (.num subjAgr.num)
    | .GEND, .idx .susan => some (.gend subjAgr.gend)
    | .PER, .idx .pron => some (.per objAgr.per)
    | .NUM, .idx .pron => some (.num objAgr.num)
    | .GEND, .idx .pron => some (.gend objAgr.gend)
    | _, _ => none
  R ρ := ρ.elim

/-- The worked transitive clause, whose verb has *Susan* and the pronoun on its argument
structure. -/
abbrev clause (pronSort : Binding.Srt) (pronIdx : Syn) (subjAgr objAgr : Agr) :
    Interpretation Binding.sig Ent :=
  utterance ![[.susan, .pron], []] pronSort pronIdx subjAgr objAgr


instance (args : Fin 2 → List Syn) (σ : Binding.Srt) (i : Syn) (x y : Agr)
    (ρ : Binding.sig.Rel) : DecidablePred (· ∈ (utterance args σ i x y).R ρ) :=
  ρ.elim

variable {args : Fin 2 → List Syn} {σ : Binding.Srt} {i : Syn} {x y : Agr}

/-- `a` precedes `b` among the first three members of the list `l`. -/
def PrecedesOn (l : List Syn) (a b : Syn) : Prop :=
  ∃ m n : Fin 3, m < n ∧ l[m.val]? = some a ∧ l[n.val]? = some b

/-- `a` precedes `b` on one of the argument structures. -/
def Precedes (args : Fin 2 → List Syn) (a b : Syn) : Prop := ∃ k, PrecedesOn (args k) a b

instance (l : List Syn) (a b : Syn) : Decidable (PrecedesOn l a b) :=
  inferInstanceAs (Decidable (∃ m n : Fin 3, m < n ∧ l[m.val]? = some a ∧ l[n.val]? = some b))

instance (a b : Syn) : Decidable (Precedes args a b) :=
  inferInstanceAs (Decidable (∃ k, PrecedesOn (args k) a b))

theorem PrecedesOn.mem_right {l : List Syn} {a b : Syn} (h : PrecedesOn l a b) : b ∈ l :=
  let ⟨_, _, _, _, hb⟩ := h; List.mem_of_getElem? hb

theorem argAt_utterance (w : Ent) (m : Fin 3) :
    Binding.argAt (utterance args σ i x y) w m =
      match w with
      | .word k => (args k)[m.val]?.map .syn
      | _ => none := by
  cases w with
  | word k =>
    show Binding.argAt (utterance args σ i x y) (.word k) m = (args k)[m.val]?.map .syn
    rcases hk : args k with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
      revert m <;> simp [Fin.forall_fin_succ, Binding.argAt, hk]
  | _ => revert m; simp [Fin.forall_fin_succ, Binding.argAt]

/-- Within an entity of a worked utterance, local o-command is precedence on the argument
structure of a word that is one of its components. -/
theorem locallyOCommandsWithin_utterance_iff {u z w : Ent} :
    Binding.LocallyOCommandsWithin (utterance args σ i x y) u z w ↔
      ∃ k, (utterance args σ i x y).IsComponentOf u (.word k) ∧
        ∃ a b, z = .syn a ∧ w = .syn b ∧ PrecedesOn (args k) a b := by
  simp only [Binding.LocallyOCommandsWithin, argAt_utterance, PrecedesOn]
  constructor
  · rintro ⟨v, hv, m, n, hmn, hz, hw⟩
    cases v with
    | word k =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hz
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hw
      exact ⟨k, hv, a, b, rfl, rfl, m, n, hmn, ha, hb⟩
    | _ => simp at hz
  · rintro ⟨k, hk, a, b, rfl, rfl, m, n, hmn, ha, hb⟩
    exact ⟨.word k, hk, m, n, hmn, by simp [ha], by simp [hb]⟩

theorem isComponentOf_root_word (k : Fin 2) :
    (utterance args σ i x y).IsComponentOf .root (.word k) := by
  have h₀ : (utterance args σ i x y).IsComponentOf .root (.dtrs 0) := .single ⟨.DTRS, rfl⟩
  revert k
  rw [Fin.forall_fin_two]
  exact ⟨h₀.tail ⟨.FIRST, rfl⟩, (h₀.tail ⟨.REST, rfl⟩).tail ⟨.FIRST, rfl⟩⟩

theorem isComponentOf_root_syn {k : Fin 2} {a b : Syn} (h : PrecedesOn (args k) a b) :
    (utterance args σ i x y).IsComponentOf .root (.syn b) := by
  obtain ⟨_, n, _, _, hb⟩ := h
  exact Binding.isComponentOf_of_argAt (isComponentOf_root_word k)
    ((argAt_utterance (.word k) n).trans (by simp [hb]))

/-- At the root of a worked utterance, local o-command is precedence on one of the argument
structures. -/
theorem locallyOCommandsWithin_root_iff {z w : Ent} :
    Binding.LocallyOCommandsWithin (utterance args σ i x y) .root z w ↔
      ∃ a b, z = .syn a ∧ w = .syn b ∧ Precedes args a b := by
  rw [locallyOCommandsWithin_utterance_iff]
  exact ⟨fun ⟨k, _, a, b, hz, hw, h⟩ ↦ ⟨a, b, hz, hw, k, h⟩,
    fun ⟨a, b, hz, hw, k, h⟩ ↦ ⟨k, isComponentOf_root_word k, a, b, hz, hw, h⟩⟩

/-- The member `a` of an argument structure has the index of the pronoun, whose index is that of
`i`. -/
def Shares (i : Syn) : Syn → Prop
  | .pron => True
  | .clause => False
  | a => a = i

instance (i a : Syn) : Decidable (Shares i a) := by
  cases a <;> unfold Shares <;> infer_instance

theorem coindexed_syn_pron (a : Syn) :
    Binding.Coindexed (utterance args σ i x y) (.syn a) (.syn .pron) ↔ Shares i a := by
  cases a <;> simp [Binding.Coindexed, Shares, eq_comm]

theorem sort_syn_eq_iff {b : Syn} {τ : Binding.Srt} (hτ : τ = .ana ∨ τ = .ppro) :
    (utterance args σ i x y).S (.syn b) = τ ↔ b = .pron ∧ σ = τ := by
  rcases hτ with rfl | rfl <;> cases b <;> simp

/-- The pronoun is locally o-bound: something that precedes it on an argument structure has its
index. -/
def Bound (args : Fin 2 → List Syn) (i : Syn) : Prop := ∃ a, Precedes args a .pron ∧ Shares i a

instance : Decidable (Bound args i) :=
  inferInstanceAs (Decidable (∃ a, Precedes args a .pron ∧ Shares i a))

/-- An utterance is grammatical when it satisfies the binding principles at its root. -/
def Grammatical (I : Interpretation Binding.sig Ent) : Prop :=
  ∀ d ∈ Binding.grammar, I.Satisfies (fun _ ↦ .root) .root d

/-- A worked utterance satisfies the binding principles at its root exactly when its pronoun, if
an anaphor that something precedes on an argument structure, is locally o-bound, and, if a
personal pronoun, is not. -/
theorem grammatical_utterance_iff :
    Grammatical (utterance args σ i x y) ↔
      (σ = .ana → (∃ a, Precedes args a .pron) → Bound args i) ∧ (σ = .ppro → ¬ Bound args i) := by
  rw [Grammatical, Binding.satisfies_grammar_iff_within]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨fun hσ ⟨a, ha⟩ ↦ ?_, fun hσ ⟨a, ha, hs⟩ ↦ ?_⟩
    · have hw : Binding.LocallyOCommandsWithin (utterance args σ i x y) .root (.syn a)
          (.syn .pron) := locallyOCommandsWithin_root_iff.2 ⟨a, .pron, rfl, rfl, ha⟩
      obtain ⟨k, hk⟩ := ha
      obtain ⟨z, hz, hc⟩ := hA (.syn .pron) (isComponentOf_root_syn hk)
        ((sort_syn_eq_iff (.inl rfl)).2 ⟨rfl, hσ⟩) _ hw
      obtain ⟨c, b, rfl, hb, hcb⟩ := locallyOCommandsWithin_root_iff.1 hz
      obtain rfl : b = .pron := by simpa using hb.symm
      exact ⟨c, hcb, (coindexed_syn_pron c).1 hc⟩
    · have hw : Binding.LocallyOCommandsWithin (utterance args σ i x y) .root (.syn a)
          (.syn .pron) := locallyOCommandsWithin_root_iff.2 ⟨a, .pron, rfl, rfl, ha⟩
      obtain ⟨k, hk⟩ := ha
      exact hB (.syn .pron) (isComponentOf_root_syn hk)
        ((sort_syn_eq_iff (.inr rfl)).2 ⟨rfl, hσ⟩) _ hw ((coindexed_syn_pron a).2 hs)
  · rintro ⟨hA, hB⟩
    refine ⟨fun e _ he z hz ↦ ?_, fun e _ he z hz hc ↦ ?_⟩
    · obtain ⟨a, b, rfl, rfl, hab⟩ := locallyOCommandsWithin_root_iff.1 hz
      obtain ⟨rfl, hσ⟩ := (sort_syn_eq_iff (.inl rfl)).1 he
      obtain ⟨c, hc, hs⟩ := hA hσ ⟨a, hab⟩
      exact ⟨.syn c, locallyOCommandsWithin_root_iff.2 ⟨c, .pron, rfl, rfl, hc⟩,
        (coindexed_syn_pron c).2 hs⟩
    · obtain ⟨a, b, rfl, rfl, hab⟩ := locallyOCommandsWithin_root_iff.1 hz
      obtain ⟨rfl, hσ⟩ := (sort_syn_eq_iff (.inr rfl)).1 he
      exact hB hσ ⟨a, hab, (coindexed_syn_pron a).1 hc⟩

/-- Where the pronoun is on one argument structure only, a worked utterance is a model of the
binding grammar, every entity satisfying the principles over its own components, exactly when it
satisfies them at its root. -/
theorem models_utterance_iff (hone : ∀ k k', Syn.pron ∈ args k → Syn.pron ∈ args k' → k = k') :
    (utterance args σ i x y).Models Binding.grammar ↔ Grammatical (utterance args σ i x y) := by
  refine ⟨fun h d hd ↦ h d hd _ _, fun h ↦ Interpretation.models_iff.2 fun d hd u ↦ ?_⟩
  obtain ⟨hA, hB⟩ := grammatical_utterance_iff.1 h
  revert d
  rw [Binding.satisfies_grammar_iff_within]
  refine ⟨fun e _ he z hz ↦ ?_, fun e _ he z hz hc ↦ ?_⟩
  · obtain ⟨k, hk, a, b, rfl, rfl, hab⟩ := locallyOCommandsWithin_utterance_iff.1 hz
    obtain ⟨rfl, hσ⟩ := (sort_syn_eq_iff (.inl rfl)).1 he
    obtain ⟨c, ⟨k', hc⟩, hs⟩ := hA hσ ⟨a, k, hab⟩
    obtain rfl := hone k k' hab.mem_right hc.mem_right
    exact ⟨.syn c, locallyOCommandsWithin_utterance_iff.2 ⟨k, hk, c, .pron, rfl, rfl, hc⟩,
      (coindexed_syn_pron c).2 hs⟩
  · obtain ⟨k, hk, a, b, rfl, rfl, hab⟩ := locallyOCommandsWithin_utterance_iff.1 hz
    obtain ⟨rfl, hσ⟩ := (sort_syn_eq_iff (.inr rfl)).1 he
    exact hB hσ ⟨a, ⟨k, hab⟩, (coindexed_syn_pron a).1 hc⟩

/-- The sort of a row's pronoun. -/
def Examples.PronounSort.toSrt : Examples.PronounSort → Binding.Srt
  | .anaphor => .ana
  | .pronoun => .ppro

/-- The argument structures of a row's two words. A prepositional object stands in the place of
its PP, the two being of equal rank; a second word is the verb of the embedded clause or the
noun of the subject. -/
def Examples.Frame.argStructures : Examples.Frame → Fin 2 → List Syn
  | .transitive => ![[.susan, .pron], []]
  | .doubleObject => ![[.susan, .pron, .other], []]
  | .toDative => ![[.susan, .other, .pron], []]
  | .objectAndPP => ![[.susan, .pron, .other], []]
  | .objectAntecedent => ![[.other, .susan, .pron], []]
  | .embedded => ![[.susan, .clause], [.other, .pron]]
  | .possessor => ![[.other, .pron], [.susan]]
  | .pictureNoun => ![[.other, .pron], [.susan]]

theorem pron_mem_args_unique : ∀ f : Examples.Frame, ∀ k k',
    Syn.pron ∈ f.argStructures k → Syn.pron ∈ f.argStructures k' → k = k' := by
  decide

theorem utterance_isWellTyped : ∀ f : Examples.Frame, ∀ s : Examples.PronounSort,
    (utterance f.argStructures s.toSrt .susan .susan .susan).IsWellTyped := by
  decide +kernel

/-- With the pronoun coindexed with *Susan*, each sentence is acceptable exactly when its
utterance satisfies the binding principles, local o-command being read off the argument
structures. -/
theorem binding_rows :
    ∀ e ∈ probing .binding, ∀ s ∈ Examples.sort e, ∀ f ∈ Examples.frame e,
      (e.judgment = .acceptable ↔
        Grammatical (utterance f.argStructures s.toSrt .susan .susan .susan)) := by
  simp only [grammatical_utterance_iff]
  decide

/-- The utterances of the acceptable sentences are models of the binding grammar, every entity
satisfying the principles over its own components. -/
theorem binding_rows_models :
    ∀ e ∈ probing .binding, ∀ s ∈ Examples.sort e, ∀ f ∈ Examples.frame e,
      (e.judgment = .acceptable ↔
        (utterance f.argStructures s.toSrt .susan .susan .susan).Models Binding.grammar) := by
  intro e he s hs f hf
  rw [models_utterance_iff (pron_mem_args_unique f)]
  exact binding_rows e he s hs f hf

theorem clause_satisfies_conditions :
    let I := (clause .ana .susan .susan .susan).generated .root
    (Binding.configuration I).Satisfies (Binding.Coindexed I) (Binding.configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  Binding.satisfies_of_models
    (((models_utterance_iff (pron_mem_args_unique .transitive)).2
      (grammatical_utterance_iff.2 (by decide))).generated .root)
    Interpretation.isRootedAt_generated fun _ h ↦ by
      obtain ⟨k, _, a, b, ha, hb, hab⟩ := locallyOCommandsWithin_utterance_iff.1
        (Binding.locallyOCommands_generated_iff.1 h)
      obtain rfl : a = b := by simpa using ha.symm.trans hb
      exact (by decide : ∀ k a, ¬ PrecedesOn ((![[.susan, .pron], []] : Fin 2 → List Syn) k) a a)
        k a hab

/-! ### Pronominal agreement -/

/-- The agreement bundle of an index with the values `x`. -/
def Agr.bundle (x : Agr) : Agreement.Bundle :=
  Binding.agreement (clause .ana .susan x x) (.syn .susan)

/-- A subject whose form has the agreement bundle `a` and a reflexive object whose form has the
bundle `r` are licensed when one index bears the person, number and gender of both forms. The
index of a bundle is its person, number and gender, the features an HPSG index bears; a form's
case is not among them. -/
def Licenses (a r : Agreement.Bundle) : Prop :=
  ∃ x : Agr, a.index ≤ x.bundle.index ∧ r.index ≤ x.bundle.index

instance (a r : Agreement.Bundle) : Decidable (Licenses a r) :=
  inferInstanceAs (Decidable (∃ _ : Agr, _ ∧ _))

theorem agreement_subj (i : Syn) (x y : Agr) :
    Binding.agreement (clause .ana i x y) (.syn .susan) = x.bundle := by
  funext d; cases d <;> rfl

theorem agreement_obj_susan (x y : Agr) :
    Binding.agreement (clause .ana .susan x y) (.syn .pron) = x.bundle := by
  funext d; cases d <;> rfl

/-- A clause with a reflexive object is grammatical exactly when the reflexive has the subject's
index, whatever the values of the indices. -/
theorem grammatical_clause_ana_iff {i : Syn} (hi : i ∈ [Syn.susan, .pron]) (x y : Agr) :
    Grammatical (clause .ana i x y) ↔ i = .susan := by
  rw [grammatical_utterance_iff]
  obtain rfl | rfl : i = .susan ∨ i = .pron := by simpa using hi
  · exact iff_of_true (by decide) rfl
  · exact iff_of_false (by decide) (by decide)

/-- A subject and a reflexive object are licensed exactly when some worked clause is grammatical
in which the subject's agreement bundle extends the subject form's index and the object's the
reflexive form's. -/
theorem licenses_iff_exists_grammatical {a r : Agreement.Bundle} :
    Licenses a r ↔ ∃ i ∈ [Syn.susan, .pron], ∃ x y : Agr,
      a.index ≤ (Binding.agreement (clause .ana i x y) (.syn .susan)).index ∧
        r.index ≤ (Binding.agreement (clause .ana i x y) (.syn .pron)).index ∧
          Grammatical (clause .ana i x y) := by
  refine ⟨fun ⟨x, ha, hr⟩ ↦ ⟨.susan, by simp, x, x, ?_, ?_,
      (grammatical_clause_ana_iff (by simp) x x).2 rfl⟩,
    fun ⟨i, hi, x, y, ha, hr, hG⟩ ↦ ?_⟩
  · exact (agreement_subj _ x x).symm ▸ ha
  · exact (agreement_obj_susan x x).symm ▸ hr
  · obtain rfl := (grammatical_clause_ana_iff hi x y).1 hG
    exact ⟨x, agreement_subj _ x y ▸ ha, agreement_obj_susan x y ▸ hr⟩

/-- With no agreement condition in the binding principles, an English reflexive is licensed with
a pronoun antecedent exactly when the indices of their agreement bundles are compatible:
Principle A requires the two to share an index, and an index has one person, number and
gender. -/
theorem licenses_iff_compat :
    ∀ a ∈ English.Pronouns.personal, ∀ r ∈ English.Pronouns.reflexives,
      (Licenses a.agreement r.agreement ↔ Compat a.agreement.index r.agreement.index) := by
  decide +kernel

-- (17a)–(17c)
theorem agreement_rows :
    ∀ e ∈ probing .pronominalAgreement,
      ∀ a ∈ English.Pronouns.personal, e.feature? "antecedent" = some a.form →
        ∀ r ∈ English.Pronouns.reflexives, e.feature? "reflexive" = some r.form →
          (e.judgment = .acceptable ↔ Licenses a.agreement r.agreement) := by
  decide +kernel

/-- Nominal objects with the same agreement bundle need not be coindexed: in *Susan likes her*
with *her* another woman the two indices have the same values and the clause is grammatical. -/
theorem agreement_eq_not_coindexed :
    Binding.agreement (clause .ppro .pron .susan .susan) (.syn .susan) =
        Binding.agreement (clause .ppro .pron .susan .susan) (.syn .pron) ∧
      ¬ Binding.Coindexed (clause .ppro .pron .susan .susan) (.syn .susan) (.syn .pron) ∧
        Grammatical (clause .ppro .pron .susan .susan) :=
  ⟨by funext d; cases d <;> rfl, by decide, grammatical_utterance_iff.2 (by decide)⟩

/-! ### Long-distance dependencies -/

/-- In the coordination construction the two conjuncts share their category and GAP list, and
the mother carries them. -/
def coordinationPrinciple : Constraint sig where
  sort := .coordCxt
  body :=
    .and (.pathEq (.path [.CONJ1, .CAT]) (.path [.CONJ2, .CAT]))
      (.and (.pathEq (.path [.CONJ1, .GAP]) (.path [.CONJ2, .GAP]))
        (.and (.pathEq (.path [.MTR, .CAT]) (.path [.CONJ1, .CAT]))
          (.pathEq (.path [.MTR, .GAP]) (.path [.CONJ1, .GAP]))))

/-- The filler-gap grammar with the coordination construction. -/
abbrev swbGrammar : Grammar sig :=
  .ofList ((constraints ++ [coordinationPrinciple]).map Constraint.toDescription)

/-- The entities of a worked coordinate construct are the construct, its mother and two
conjuncts, their category, a one-gap list with its NP gap and the gap's index, and the empty
list. -/
inductive CoordEnt where
  | cxt
  | mtr
  | c₁
  | c₂
  | cat
  | np
  | g
  | gp
  | nil
  | ix
  deriving DecidableEq, Fintype, Repr

/-- The GAP list of a conjunct is the shared one-gap list when the conjunct contains a gap, and
the empty list otherwise. -/
def gapList (b : Bool) : CoordEnt := if b then .g else .nil

/-- A coordinate construct of two clausal conjuncts, each containing a gap or not. The gap is one
NP, shared by the conjuncts that have one, and the mother's GAP is the first conjunct's. -/
@[reducible] def coordConstruct (gap₁ gap₂ : Bool) : Interpretation sig CoordEnt where
  S := fun
    | .cxt => .coordCxt
    | .mtr | .c₁ | .c₂ => .overtExpr
    | .cat => .verb
    | .np => .noun
    | .g => .nelist
    | .gp => .gap
    | .nil => .elist
    | .ix => .idx
  A := fun a u ↦ match a, u with
    | .MTR, .cxt => some .mtr
    | .CONJ1, .cxt => some .c₁
    | .CONJ2, .cxt => some .c₂
    | .CAT, .mtr | .CAT, .c₁ | .CAT, .c₂ => some .cat
    | .GAP, .mtr | .GAP, .c₁ => some (gapList gap₁)
    | .GAP, .c₂ => some (gapList gap₂)
    | .FIRST, .g => some .gp
    | .REST, .g => some .nil
    | .CAT, .gp => some .np
    | .INDEX, .gp => some .ix
    | _, _ => none
  R := noRel

theorem coordConstruct_isWellTyped (g₁ g₂ : Bool) : (coordConstruct g₁ g₂).IsWellTyped := by
  cases g₁ <;> cases g₂ <;> decide

theorem coordination_rows :
    ∀ x ∈ probing .coordination, ∀ g₁ ∈ x.bool? "gapInFirst",
      ∀ g₂ ∈ x.bool? "gapInSecond",
        (x.judgment = .acceptable ↔ (coordConstruct g₁ g₂).Models swbGrammar) := by
  decide +kernel

theorem gap_not_conjunct {U : Type*} {I : Interpretation sig U} (hI : I.IsWellTyped) {u v : U}
    (hv : I.A .CONJ1 u = some v) : ¬ I.S v ≤ .gap :=
  fun h ↦ not_le_covertExpr hI (by simp) hv (h.trans (by decide))

end SagWasowBender2003
