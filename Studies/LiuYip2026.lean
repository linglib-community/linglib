module

public import Linglib.Syntax.Minimalist.Category.FunctionalSequence
public import Linglib.Syntax.Minimalist.Clause.Size
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Fragments.Mandarin.Adverbs
public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Fragments.Cantonese.Aspect
public import Linglib.Fragments.Cantonese.Particles
public import Linglib.Fragments.Cantonese.Verbs
public import Linglib.Fragments.Cantonese.ResultativeComplements

/-!
# Liu and Yip (2026): Again, finiteness, and split aspect in Chinese languages

This file formalizes the size-based account of finiteness and of exceptional scope in
Liu and Yip's paper. Verb complements in Mandarin and Cantonese come in three sizes, a finite CP, a
nonfinite TP and a nonfinite vP, and the two aspect projections of the split aspect approach
sit at fixed heights, the outer one at the level of T above vP and the inner one at the level
of v, so every complement contains inner aspect and only a TP or larger contains outer aspect
(`Contains`). An *again*-element or aspectual suffix associates with one of the two
projections, by movement for Mandarin preverbal *you* and by agreement for the suffixes, and
takes exceptional scope across a complement, skipping the matrix predicate or lowering onto it,
exactly when the complement has no projection of its kind to intervene, so that it
associates with the matrix one (`ExceptionalScope`). The paper's tables follow from that one
definition: outer-associated elements, Mandarin *you*, Cantonese *-faan* and the outer
aspectual suffixes, take exceptional scope across a vP and across nothing larger
(`exceptionalScope_outer_iff`); inner-associated elements, Mandarin *zai*, Cantonese *zoi* and
repetitive *-gwo*, the continuous *-zyu* and the phase complements, never do
(`not_exceptionalScope_inner`), which is the argument that vP is the minimal size of a nonfinite
clause; and transparency is downward closed along the size hierarchy
(`antitone_exceptionalScope`), the implicational complementation hierarchy of
Wurmbrand and Lohninger. A Cantonese nonfinite complement is a vP or a TP and a finite one a CP
(`sizes`), so *-faan* embedded under a verb takes wide scope over it exactly when the verb's frame
in the fragment is nonfinite, and then ambiguously (`faan_crossesComplement_iff`,
`faan_ambiguous`), which sorts the fragment's verbs into the paper's two lists (`faan_lowering`).
Mandarin *you* alone carries the unvalued dynamic feature of
Lin and Liu and must be licensed by an outer aspect head bearing `[+D]`, which the paper's
selectional table for *xiang* 'want', *rang* 'let' and *xiangxin* 'believe' turns into the
embeddability of *you* (`Pred.embedsYou`) and into the blocking of aspect lowering by an embedded
*you* (`not_exceptionalScope_of_licensesDynamic`).

## Main definitions

* `AspProjection`, `AspProjection.level` — the outer and inner aspect projections of the split
  aspect approach and their heights in the functional sequence.
* `Contains`, `ExceptionalScope` — a complement size contains an aspect projection, and an
  element associated with it takes exceptional scope across it.
* `Again`, `Again.projection`, `Again.NeedsDynamic` — the six *again*-elements, the projection each
  associates with, and the dynamic feature of *you*.
* `aspectProjection`, `phaseComplementProjection` — the association of the Cantonese aspect suffixes
  and phase complements.
* `Pred.selects`, `Complement.LicensesDynamic` — the complements the Mandarin predicates select.
* `sizes`, `Again.CrossesComplement` — the sizes of a Cantonese complement by its finiteness, and
  the exceptional scope of an element across the complement of a verb.

## Main results

* `exceptionalScope_outer_iff`, `not_exceptionalScope_inner`, `antitone_exceptionalScope` — the
  scope pattern by size and projection, and the implicational hierarchy.
* `faan_crossesComplement_iff`, `not_gwo_crossesComplement`, `faan_ambiguous`, `faan_lowering` —
  *-faan* lowering onto the verbs with a nonfinite complement, ambiguously, and *-gwo* lowering
  onto none.
* `generalization_I`, `generalization_II`, `correlation_I`, `correlation_II` — the Mandarin
  generalizations as consequences.
* `cantonese_lowering`, `aspect_lowering`, `no_phaseComplement_lowering` — the Cantonese
  pattern for the *again*-elements, the aspect suffixes and the phase complements.
* `embedsYou`, `not_exceptionalScope_of_licensesDynamic` — the licensing of *you* and its
  blocking of aspect lowering.

## Implementation notes

The two projections are the binary split of Travis, MacDonald, Tsai and Sybesma; their
heights are those of the functional sequence in `Syntax/Minimalist/Category/FunctionalSequence`,
outer aspect at the level of T and inner aspect at the level of v, so containment is a
comparison of levels. Chomsky's defective intervention is not a
relation between heads: an embedded projection blocks association whatever its features, which
is the paper's claim. The semicomplementizer and Exfoliation, the restitutive reading, the
Italian parallel and the crosstype ambiguity of *dasuan* 'plan' are not represented.

## References

* [liu-yip-2026]
* [wurmbrand-lohninger-2023]
* [lin-liu-2009]
* [chomsky-2000]
* [travis-2010]
* [macdonald-2008]
* [tsai-2008]
* [sybesma-2017]
-/

@[expose] public section

namespace LiuYip2026

open Minimalist

/-! ### Clause sizes and the projections they contain -/

/-- The split aspect approach has two aspect projections, the outer one above vP, which hosts
viewpoint aspect, and the inner one in the v shell, which hosts Aktionsart. -/
inductive AspProjection where
  | outer
  | inner
  deriving DecidableEq, Repr

/-- The height of a projection in the functional sequence, the level of T for the outer one and
of v for the inner one. -/
def AspProjection.level : AspProjection → ℕ
  | .outer => Cat.fValue .T
  | .inner => Cat.fValue .v

/-- Type I, the finite CP. -/
def typeI : ComplementSize := .cP

/-- Type II, the nonfinite TP without aspect restructuring. -/
def typeII : ComplementSize := .tP

/-- Type III, the nonfinite vP with aspect restructuring. -/
def typeIII : ComplementSize := .vP

/-- A complement of size `s` contains the aspect projection `f` when it reaches the
projection's height, the level of T for the outer one and the level of v for the inner one. -/
def Contains (s : ComplementSize) (f : AspProjection) : Prop := f.level ≤ s.fLevel

instance (s : ComplementSize) (f : AspProjection) : Decidable (Contains s f) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem contains_inner {s : ComplementSize} (h : ComplementSize.vP ≤ s) : Contains s .inner := h

theorem contains_outer_iff (s : ComplementSize) : Contains s .outer ↔ ComplementSize.tP ≤ s :=
  Iff.rfl

/-- An element associated with the projection `f` takes exceptional scope across a
complement of size `s`, skipping the matrix predicate or lowering onto it, when the complement
has no projection of that kind to intervene, so that the element associates with the matrix
one. -/
def ExceptionalScope (f : AspProjection) (s : ComplementSize) : Prop := ¬ Contains s f

instance (f : AspProjection) (s : ComplementSize) : Decidable (ExceptionalScope f s) :=
  inferInstanceAs (Decidable (¬ _))

/-- Transparency is downward closed along the size hierarchy, the implicational complementation
hierarchy, so what crosses a larger complement crosses a smaller one. -/
theorem antitone_exceptionalScope (f : AspProjection) : Antitone (ExceptionalScope f) :=
  fun _ _ h hs hc ↦ hs (hc.trans h)

/-- Outer-associated elements take exceptional scope across a complement smaller than a TP,
the vP, and across nothing larger. -/
theorem exceptionalScope_outer_iff (s : ComplementSize) :
    ExceptionalScope .outer s ↔ s < ComplementSize.tP :=
  Nat.not_le

/-- Inner-associated elements never take exceptional scope, since every complement contains
inner aspect, so vP is the minimal size of a nonfinite clause. -/
theorem not_exceptionalScope_inner {s : ComplementSize} (h : ComplementSize.vP ≤ s) :
    ¬ ExceptionalScope .inner s :=
  fun hs ↦ hs (contains_inner h)

/-- Generalization II says that exceptional scope crosses a nonfinite vP, not a nonfinite TP nor
a finite CP. -/
theorem generalization_II :
    ExceptionalScope .outer typeIII ∧ ¬ ExceptionalScope .outer typeII ∧
      ¬ ExceptionalScope .outer typeI := by
  decide

/-- The sizes a clausal complement of the frame can have, a CP (Type I) for a finite clause and
a TP (Type II) or a vP (Type III) for a nonfinite one. -/
def sizes (fr : ArgumentFrame) : Finset ComplementSize :=
  if fr.HasFinite then {typeI} else if fr.HasClausal then {typeIII, typeII} else ∅

theorem vP_le_of_mem_sizes {fr : ArgumentFrame} {s : ComplementSize} (h : s ∈ sizes fr) :
    ComplementSize.vP ≤ s := by
  unfold sizes at h
  split_ifs at h <;> simp only [Finset.mem_singleton, Finset.mem_insert,
    Finset.notMem_empty] at h <;> rcases h with rfl | rfl <;> decide

theorem exists_mem_sizes_exceptionalScope_outer_iff (fr : ArgumentFrame) :
    (∃ s ∈ sizes fr, ExceptionalScope .outer s) ↔ fr.HasClausal ∧ ¬ fr.HasFinite := by
  unfold sizes
  split_ifs <;> simp_all <;> decide

/-! ### The *again*-elements and their projections -/

/-- The *again*-type elements of the two languages, Mandarin preverbal *you* and *zai*,
Cantonese preverbal *jau* and *zoi* and postverbal *-faan* and repetitive *-gwo*. -/
inductive Again where
  | you
  | zai
  | jau
  | zoi
  | faan
  | gwo
  deriving DecidableEq, Repr

/-- The lexical entry of an element in its language's fragment. -/
def Again.item : Again → Presupposition.TriggerItem
  | .you => Mandarin.Adverbs.you
  | .zai => Mandarin.Adverbs.zai
  | .jau => Cantonese.Particles.jau
  | .zoi => Cantonese.Particles.zoi
  | .faan => Cantonese.Particles.faan
  | .gwo => Cantonese.Particles.gwo

theorem Again.item_triggerClass (a : Again) : a.item.triggerClass = .iterative := by cases a <;> rfl

/-- The projection each element associates with. *You* associates by movement and *-faan* by
agreement with the outer one, and *zai*, *zoi* and repetitive *-gwo* with the inner one;
preverbal *jau* is base-generated where it is pronounced and associates with neither. -/
def Again.projection : Again → Option AspProjection
  | .you | .faan => some .outer
  | .zai | .zoi | .gwo => some .inner
  | .jau => none

/-- The element carries the unvalued dynamic feature `[u+D]` that an outer aspect head bearing
`[+D]` must check, which *you* alone does. -/
def Again.NeedsDynamic (a : Again) : Prop := a = .you

instance : DecidablePred Again.NeedsDynamic := fun a ↦ inferInstanceAs (Decidable (a = .you))

/-- The element takes exceptional scope across some complement. -/
def Again.Skips (a : Again) : Prop :=
  ∃ f ∈ a.projection, ∃ s ∈ [typeI, typeII, typeIII], ExceptionalScope f s

instance : DecidablePred Again.Skips := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem skips_iff (a : Again) : a.Skips ↔ a.projection = some .outer := by cases a <;> decide

/-- Generalization I says that exceptional scope is found with *you* but not with *zai*. -/
theorem generalization_I : Again.you.Skips ∧ ¬ Again.zai.Skips := by decide

/-- In Cantonese *-faan* lowers, repetitive *-gwo* does not, and neither preverbal adverb has
exceptional scope. -/
theorem cantonese_lowering :
    Again.faan.Skips ∧ ¬ Again.gwo.Skips ∧ ¬ Again.jau.Skips ∧ ¬ Again.zoi.Skips := by
  decide

/-- Correlation I says that a Mandarin *again*-element has exceptional scope iff it cannot
surface in an embedded nonfinite clause without a dynamic aspect, that is, iff it carries
`[u+D]`. -/
theorem correlation_I : ∀ a ∈ [Again.you, Again.zai], (a.Skips ↔ a.NeedsDynamic) := by decide

/-- Correlation II says that an *again*-element has exceptional scope iff its projection is at
least as high as the aspectual heads, the level of `Asp` in the functional sequence. -/
theorem correlation_II (a : Again) :
    a.Skips ↔ ∃ f ∈ a.projection, Cat.fValue .Asp ≤ f.level := by
  cases a <;> decide

/-! ### Aspect suffixes and phase complements -/

/-- The Cantonese aspect suffixes associate with a projection, the perfective *-zo*, the
progressive *-gan* and the experiential *-gwo* with the outer one and the continuous *-zyu* with
the inner one. -/
def aspectProjection (m : Aspect.Marker) : AspProjection :=
  if m = Cantonese.Aspect.zyu then .inner else .outer

/-- Every phase complement associates with the inner projection. -/
def phaseComplementProjection (_ : Cantonese.ResultativeComplements.PhaseComplement) :
    AspProjection :=
  .inner

/-- Under aspect lowering an outer aspect suffix embedded in a vP is interpreted on the matrix
predicate, and the continuous *-zyu* alone is not. -/
theorem aspect_lowering :
    ∀ m ∈ Cantonese.Aspect.markers,
      (ExceptionalScope (aspectProjection m) typeIII ↔ m ≠ Cantonese.Aspect.zyu) := by
  decide

/-- No phase complement lowers across any complement. -/
theorem no_phaseComplement_lowering (pc : Cantonese.ResultativeComplements.PhaseComplement)
    {s : ComplementSize} (h : ComplementSize.vP ≤ s) :
    ¬ ExceptionalScope (phaseComplementProjection pc) s :=
  not_exceptionalScope_inner h

/-! ### Selection and the licensing of *you* -/

/-- A complement as a predicate selects it is a vP, a TP whose outer aspect head has the given
dynamicity, or a CP. -/
inductive Complement where
  | vP
  | tP (d : Aspect.Dynamicity)
  | cP
  deriving DecidableEq, Repr

/-- The size of a complement. -/
def Complement.size : Complement → ComplementSize
  | .vP => .vP
  | .tP _ => .tP
  | .cP => .cP

/-- A complement licenses a `[u+D]` element when it has an outer aspect head bearing `[+D]`, as
a dynamic TP does, and a CP, whose outer aspect head may be dynamic. -/
def Complement.LicensesDynamic (c : Complement) : Prop := c = .tP .dynamic ∨ c = .cP

instance : DecidablePred Complement.LicensesDynamic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A complement that licenses *you* contains outer aspect, so nothing outer-associated takes
exceptional scope across it, and an embedded *you* blocks aspect lowering. -/
theorem not_exceptionalScope_of_licensesDynamic {c : Complement} (h : c.LicensesDynamic) :
    ¬ ExceptionalScope .outer c.size := by
  rcases h with rfl | rfl <;> decide

/-- The three Mandarin predicates of the selectional table. -/
inductive Pred where
  | xiang
  | rang
  | xiangxin
  deriving DecidableEq, Repr

/-- The lexical entry of a predicate. -/
def Pred.entry : Pred → Verb
  | .xiang => Mandarin.xiang
  | .rang => Mandarin.rang
  | .xiangxin => Mandarin.xiangxin

/-- The complements each predicate selects. *Xiang* 'want' selects a vP or a stative TP, *rang*
'let' a vP or a TP of either dynamicity, and *xiangxin* 'believe' a CP. -/
def Pred.selects : Pred → List Complement
  | .xiang => [.vP, .tP .stative]
  | .rang => [.vP, .tP .stative, .tP .dynamic]
  | .xiangxin => [.cP]

/-- *You* can surface in a complement of the predicate iff the predicate selects a complement
licensing `[u+D]`. -/
def Pred.EmbedsYou (p : Pred) : Prop := ∃ c ∈ p.selects, c.LicensesDynamic

instance : DecidablePred Pred.EmbedsYou := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- *You* skips the predicate iff the predicate selects a vP. -/
def Pred.SkipsYou (p : Pred) : Prop := ∃ c ∈ p.selects, ExceptionalScope .outer c.size

instance : DecidablePred Pred.SkipsYou := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- In the selectional table *want* embeds no *you* but is skipped, *let* does both, and
*believe* embeds *you* and is not skipped. -/
theorem embedsYou :
    (¬ Pred.xiang.EmbedsYou ∧ Pred.xiang.SkipsYou) ∧ (Pred.rang.EmbedsYou ∧ Pred.rang.SkipsYou) ∧
      (Pred.xiangxin.EmbedsYou ∧ ¬ Pred.xiangxin.SkipsYou) := by
  decide

theorem Pred.size_mem_sizes (p : Pred) :
    ∀ c ∈ p.selects, ∃ fr ∈ p.entry.valency.frames, c.size ∈ sizes fr := by
  cases p <;> decide

theorem Pred.selects_cP_iff (p : Pred) :
    Complement.cP ∈ p.selects ↔ ∃ fr ∈ p.entry.valency.frames.head?, fr.HasFinite := by
  cases p <;> decide

/-! ### *-Faan* lowering in Cantonese -/

/-- An *again*-element takes exceptional scope across the complement of the verb, by movement
or agreement with the matrix projection, when the complement of some frame of the verb can
have a size that lacks a projection of the element's kind. -/
def Again.CrossesComplement (a : Again) (v : Verb) : Prop :=
  ∃ f ∈ a.projection, ∃ fr ∈ v.valency.frames, ∃ s ∈ sizes fr, ExceptionalScope f s

instance (a : Again) (v : Verb) : Decidable (a.CrossesComplement v) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- *-Faan* embedded under a verb takes wide scope over it exactly when some frame of the verb
has a nonfinite clausal complement. -/
theorem faan_crossesComplement_iff (v : Verb) :
    Again.faan.CrossesComplement v ↔ ∃ fr ∈ v.valency.frames, fr.HasClausal ∧ ¬ fr.HasFinite := by
  simp [Again.CrossesComplement, Again.projection, exists_mem_sizes_exceptionalScope_outer_iff]

/-- *-Gwo* associates with inner aspect, which every complement contains, so it never takes wide
scope over the verb, (72b) and (76b). -/
theorem not_gwo_crossesComplement (v : Verb) : ¬ Again.gwo.CrossesComplement v := by
  rintro ⟨f, hf, fr, -, s, hs, h⟩
  cases hf
  exact not_exceptionalScope_inner (vP_le_of_mem_sizes hs) h

/-- *-Faan* in a nonfinite complement is scopally ambiguous (93), since the complement can be a
TP, whose outer aspect head *-faan* agrees with for narrow scope, or a vP, which has none, so
that *-faan* agrees with the matrix one for wide scope. -/
theorem faan_ambiguous {fr : ArgumentFrame} (hc : fr.HasClausal) (hf : ¬ fr.HasFinite) :
    (∃ s ∈ sizes fr, Contains s .outer) ∧ ∃ s ∈ sizes fr, ExceptionalScope .outer s := by
  simp only [sizes, hf, hc, ↓reduceIte]
  decide

open Cantonese.Verbs in
/-- By their frames, the fragment's verbs fall into the paper's two lists. An embedded *-faan*
takes wide scope over the nonfinite clause-taking *soeng* 'want', *hyun* 'urge', *bik* 'force',
*giu* 'ask' and *daasyun* 'intend' (79), and not over the finite clause-taking *seon*
'believe', *gong* 'say' and *geidak* 'remember' (80). -/
theorem faan_lowering :
    (∀ v ∈ [soeng, hyun, bik, giu, daasyun], Again.faan.CrossesComplement v) ∧
      ∀ v ∈ [seon, gong, geidak], ¬ Again.faan.CrossesComplement v := by
  decide

/-! ### The implicational complementation hierarchy -/

/-- The minimal size of each semantic class of the hierarchy: vP for an event, TP for a
situation and CP for a proposition. -/
def minimalSize : Clause.Size → ComplementSize
  | .event => .vP
  | .situation => .tP
  | .proposition => .cP

theorem monotone_minimalSize : Monotone minimalSize := by decide

theorem exceptionalScope_of_le {f : AspProjection} {c c' : Clause.Size} (h : c ≤ c')
    (hs : ExceptionalScope f (minimalSize c')) : ExceptionalScope f (minimalSize c) :=
  antitone_exceptionalScope f (monotone_minimalSize h) hs

end LiuYip2026
