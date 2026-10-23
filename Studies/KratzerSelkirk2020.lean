module

public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Focus.Marking
public import Studies.HartmannZimmermann2007

/-!
# Kratzer and Selkirk (2020): Deconstructing Information Structure

Kratzer and Selkirk decompose information structure into two privative features, with their
semantics in Rooth's alternative semantics. [FoC] makes the alternatives of a constituent the whole
domain of its type and imposes no discourse requirement of its own. The squiggle that must
c-command it requires its scope to represent a contrast with each of a set of discourse referents
(49), and then collapses the alternatives to the ordinary value. [G] requires its node to be Given
with respect to a referent of the preceding discourse and leaves both values unchanged; the
requirement is use-conditional, like the German particles *ja* and *doch*. Newness is no feature
at all, so the paper's footnote on Hausa rereads the in situ and ex situ answers of Hartmann and
Zimmermann as unmarked newness and [FoC].

Two consequences follow. No constituent bears both features, since no domain is a singleton, and a
constituent containing a FoCus can be Given only if an operator inside it consumes the
alternatives (58). Through a context with no squiggle, the meaning of a constituent is the meaning
of the FoCus bound into the context, so the constituent is Given only if its ordinary value
ignores the FoCus. The paper's derivation of (58) assumes that it never does, but *[Mary]FoC came
or didn't come* is Given with an unconsumed FoCus. In second-occurrence focus (60) the squiggle
under *only* consumes the alternatives, and without it the [G] on the VP is not licensed.

## Main definitions

* `LF`, `LF.meaning`: logical forms with labelled nodes, and their meanings.
* `LF.IsVariant`, `LF.RepresentsContrast`: [FoC]/[G]-variants, and contrast representation (49).
* `Window`, `LF.Felicitous`: discourse windows, and the use-conditional content of [G] and the
  squiggle.
* `LF.Ctx`, `LF.Ctx.Transparent`: one-hole contexts, and those with no squiggle.

## Main results

* `not_given_mark_focused`: no constituent bears both features.
* `LF.Ctx.meaning_plug`: a context with no squiggle is a continuation.
* `LF.ord_plug_eq_of_given`, `LF.not_given_plug_foc`: (58) at any depth.
* `LF.given_foc_came_or_not`: (58) needs the dependence on the FoCus.
* `LF.representsContrast_narrow`, `LF.not_representsContrast_overfocused`: among all their
  variants, (51) represents a contrast with (50a) and (50b) does not.
* `LF.felicitous_sofVP`, `LF.not_felicitous_without_squiggle`: second-occurrence focus (60).
* `sUnion_alternatives_every_focused`: Schwarzschild's givenness is trivially satisfied (fn. 14).

## Implementation notes

[FoC] is the substrate's F-mark `Focus.Mark.focused` and (45) is `WithAlternatives.mark`, the
domain of a type being all its values. The paper's Givenness is the substrate's
`WithAlternatives.Given`, and its *only* (56), every true member of the salient set being the
prejacent, is `Focus.Particles.atMost (· = ·)` at the set the squiggle also carries (55b), so the
paper's indirect association through two occurrences of the contextual variable is a fact about
the substrate and is not restated. The features are part of a node's label (p. 38), so every node
of a logical form carries a label, and the variants of a form are its relabellings. [G] (47) takes
its referent from the window preceding the context, with no anticipatory licensing (fn. 46), and
the squiggle (53) from the window surrounding it, since a contrast may be represented with a later
referent (fn. 58). Logical forms compose by function application only. The prosodic spell-out of
the features in English (§6–§7) is prose.

## TODO

* Pressure for [FoC]-Marking (66), with the data of (62)–(65), over the variants of a form.
* The squiggle of (60) over the whole sentence, contrasting with the preceding sentence.
* Logical forms with abstraction, where Hamblin alternatives do not distribute.

## References

* [kratzer-selkirk-2020]
* [rooth-1992] — alternatives semantics and the squiggle operator
* [schwarzschild-1999] — A-Givenness, of which the paper's Givenness is a special case
* [potts-2005] — expressive meaning
* [hartmann-zimmermann-2007] — the Hausa data of footnote 21
-/

@[expose] public section

open ConventionalImplicature (TwoDim)
open Focus (Mark)
open WithAlternatives (map₂ not_given_of_nontrivial)

namespace KratzerSelkirk2020

/-! ### The features (45)–(47) -/

/-- No constituent bears both features, since an F-marked constituent of a type with two values
is Given with respect to nothing. -/
theorem not_given_mark_focused {α : Type*} [Nontrivial α] (d : WithAlternatives α) (a : α) :
    ¬ (d.mark .focused).Given a :=
  not_given_of_nontrivial (d.nontrivial_alternatives_mark_focused) a

theorem useConditional_projects {W : Type*} (F : (W → Prop) → W → Prop)
    (atIssue requirement : W → Prop) :
    (F <$> (⟨atIssue, requirement⟩ : TwoDim W (W → Prop))).notAtIssue = requirement :=
  rfl

/-- (49) An expression `v i` represents a contrast with `a` when `a` is among its alternatives
and differs from its ordinary value, and no variant `v j` with strictly fewer alternatives has
`a` among them. The last condition prevents overfocusing. -/
def RepresentsContrast {ι γ : Type*} (v : ι → WithAlternatives γ) (i : ι) (a : γ) : Prop :=
  Focus.SquiggleInd (v i).ordinary (v i).alternatives a ∧
    ∀ j, (v j).alternatives ⊂ (v i).alternatives → a ∉ (v j).alternatives

/-! ### Logical forms

A logical form composes lexical meanings by function application, and a squiggle takes scope over
a constituent. Every node is labelled with its features, [FoC] and [G] with its referent, which
are "technically part of [its] labeling" (p. 38), so the [FoC]/[G]-variants of a form are its
relabellings (49). -/

/-- A node's label records whether it bears [FoC] and the referent of its [G], if it bears [G]. -/
structure Label (α : Type) where
  /-- Whether the node bears [FoC]. -/
  mark : Mark
  /-- The referent the node's [G] is indexed with, if it bears [G]. -/
  given : Option α

namespace Label

variable {α : Type}

/-- The label of a node with neither feature. -/
def bare : Label α := ⟨.unfeatured, none⟩

/-- The label of a [FoC]-marked node. -/
def foc : Label α := ⟨.focused, none⟩

end Label

/-- A logical form of the paper is a lexical item, a function application or a squiggle with its
antecedents, each node with its label, over meanings of each type. -/
inductive LF : Type → Type 1 where
  | lex {α : Type} (x : α) (l : Label α) : LF α
  | app {α β : Type} (f : LF (α → β)) (x : LF α) (l : Label β) : LF β
  | squiggle {α : Type} (ℭ : Set α) (t : LF α) (l : Label α) : LF α

namespace LF

variable {α β γ : Type}

/-- The label of the root. -/
def label : {α : Type} → LF α → Label α
  | _, lex _ l => l
  | _, app _ _ l => l
  | _, squiggle _ _ l => l

/-- The ordinary value of a logical form overlooks its labels and squiggles (45), (47), (54). -/
def ord : {α : Type} → LF α → α
  | _, lex x _ => x
  | _, app f x _ => f.ord x.ord
  | _, squiggle _ t _ => t.ord

/-- The meaning of a logical form. A node applies its function daughter to its argument, a
squiggle collapses the alternatives of its scope to the ordinary value (54), [FoC] on a node makes
its alternatives the whole type (45), and [G] leaves both values unchanged (47). -/
def meaning : {α : Type} → LF α → WithAlternatives α
  | _, lex x l => (WithAlternatives.unfeatured x).mark l.mark
  | _, app f x l => (f.meaning <*> x.meaning).mark l.mark
  | _, squiggle _ t l => (WithAlternatives.unfeatured t.ord).mark l.mark

/-- The meaning of the root before its own [FoC]. -/
def raw : {α : Type} → LF α → WithAlternatives α
  | _, lex x _ => .unfeatured x
  | _, app f x _ => f.meaning <*> x.meaning
  | _, squiggle _ t _ => .unfeatured t.ord

theorem meaning_eq_mark (t : LF α) : t.meaning = t.raw.mark t.label.mark := by
  cases t <;> rfl

@[simp] theorem meaning_lex_bare (x : α) : (lex x .bare).meaning = pure x := rfl

@[simp] theorem ordinary_meaning (t : LF α) : t.meaning.ordinary = t.ord := by
  induction t with
  | lex x l => simp only [meaning, ord, WithAlternatives.ordinary_mark,
      WithAlternatives.unfeatured_ordinary]
  | app f x l ihf ihx =>
    simp only [meaning, ord, WithAlternatives.ordinary_mark, WithAlternatives.ordinary_seq, ihf,
      ihx]
  | squiggle ℭ t l ih => simp only [meaning, ord, WithAlternatives.ordinary_mark,
      WithAlternatives.unfeatured_ordinary]

theorem wellFormed_meaning (t : LF α) : t.meaning.WellFormed := by
  induction t with
  | lex x l => exact (WithAlternatives.WellFormed.unfeatured x).mark _
  | app f x l ihf ihx =>
    exact (ihf.seq ihx).mark _
  | squiggle ℭ t l ih => exact (WithAlternatives.WellFormed.unfeatured _).mark _

theorem wellFormed_raw (t : LF α) : t.raw.WellFormed := by
  cases t with
  | lex x l => exact WithAlternatives.WellFormed.unfeatured x
  | app f x l =>
    exact f.wellFormed_meaning.seq x.wellFormed_meaning
  | squiggle ℭ t l => exact WithAlternatives.WellFormed.unfeatured _

theorem meaning_eq_bind (t : LF α) :
    t.meaning = t.raw >>= fun c ↦ (pure c : WithAlternatives α).mark t.label.mark := by
  rw [meaning_eq_mark, WithAlternatives.mark_eq_bind t.wellFormed_raw]

/-! ### Variants, contrast and felicity -/

/-- Two logical forms are [FoC]/[G]-variants when they are identical except for their labels
(49). -/
inductive IsVariant : {α : Type} → LF α → LF α → Prop
  | lex {α : Type} (x : α) (l l' : Label α) : IsVariant (lex x l) (lex x l')
  | app {α β : Type} {f f' : LF (α → β)} {x x' : LF α} (l l' : Label β) :
      IsVariant f f' → IsVariant x x' → IsVariant (app f x l) (app f' x' l')
  | squiggle {α : Type} (ℭ : Set α) {t t' : LF α} (l l' : Label α) :
      IsVariant t t' → IsVariant (squiggle ℭ t l) (squiggle ℭ t' l')

theorem IsVariant.refl (t : LF α) : IsVariant t t := by
  induction t with
  | lex x l => exact .lex x l l
  | app f x l ihf ihx => exact .app l l ihf ihx
  | squiggle ℭ t l ih => exact .squiggle ℭ l l ih

theorem IsVariant.ord_eq {s t : LF α} (h : IsVariant s t) : s.ord = t.ord := by
  induction h with
  | lex => rfl
  | app _ _ _ _ ihf ihx => simp only [ord, ihf, ihx]
  | squiggle _ _ _ _ ih => simp only [ord, ih]

/-- (49) over the variants of a logical form. It represents a contrast with `a` when `a` is among
its alternatives and differs from its ordinary value, and no variant with strictly fewer
alternatives has `a` among them. -/
def RepresentsContrast (t : LF α) (a : α) : Prop :=
  KratzerSelkirk2020.RepresentsContrast (fun s : {s : LF α // IsVariant s t} ↦ s.1.meaning)
    ⟨t, .refl t⟩ a

theorem representsContrast_iff {t : LF α} {a : α} :
    t.RepresentsContrast a ↔ a ∈ t.meaning.alternatives ∧ a ≠ t.ord ∧
      ∀ s, IsVariant s t → s.meaning.alternatives ⊂ t.meaning.alternatives →
        a ∉ s.meaning.alternatives := by
  simp only [RepresentsContrast, KratzerSelkirk2020.RepresentsContrast, Focus.SquiggleInd,
    ordinary_meaning, Subtype.forall, and_assoc]

end LF

/-- A context of utterance supplies discourse referents of each type, in the window preceding it
and in the window surrounding it. -/
structure Window where
  /-- The referents of the window preceding the context. -/
  preceding : ∀ α : Type, Set α
  /-- The referents of the window surrounding the context. -/
  surrounding : ∀ α : Type, Set α

/-- The label of a node of meaning `m` is licensed when its [G], if any, has its referent in the
preceding window and the node is Given with respect to it (47); there is no anticipatory [G]
(fn. 46). -/
def Label.Licensed {α : Type} (w : Window) (l : Label α) (m : WithAlternatives α) : Prop :=
  ∀ a ∈ l.given, a ∈ w.preceding α ∧ m.Given a

@[simp] theorem Label.licensed_bare {α : Type} (w : Window) (m : WithAlternatives α) :
    Label.bare.Licensed w m := nofun

@[simp] theorem Label.licensed_foc {α : Type} (w : Window) (m : WithAlternatives α) :
    Label.foc.Licensed w m := nofun

namespace LF

variable {α β γ : Type}

/-- A logical form is felicitous in a context when every label is licensed and every squiggle
represents a contrast with each of its antecedents, which the surrounding window supplies (54);
a contrast may be represented with a later referent (fn. 58). -/
def Felicitous (w : Window) : {α : Type} → LF α → Prop
  | _, lex x l => l.Licensed w (lex x l).meaning
  | _, app f x l => f.Felicitous w ∧ x.Felicitous w ∧ l.Licensed w (app f x l).meaning
  | α, squiggle ℭ t l => t.Felicitous w ∧ ℭ ⊆ w.surrounding α ∧
      (∀ a ∈ ℭ, t.RepresentsContrast a) ∧ l.Licensed w (squiggle ℭ t l).meaning

/-! ### (58) -/

/-- A one-hole context of a logical form, from a hole of type `α` up to a root of type `γ`, each
node above the hole with its label. -/
inductive Ctx : Type → Type → Type 1 where
  | hole {α : Type} : Ctx α α
  | fn {α β γ : Type} (x : LF α) (l : Label β) (K : Ctx β γ) : Ctx (α → β) γ
  | arg {α β γ : Type} (f : LF (α → β)) (l : Label β) (K : Ctx β γ) : Ctx α γ
  | squiggle {α γ : Type} (ℭ : Set α) (l : Label α) (K : Ctx α γ) : Ctx α γ

namespace Ctx

/-- The form with `t` in the hole. -/
def plug : {α γ : Type} → Ctx α γ → LF α → LF γ
  | _, _, hole, t => t
  | _, _, fn x l K, t => K.plug (.app t x l)
  | _, _, arg f l K, t => K.plug (.app f t l)
  | _, _, squiggle ℭ l K, t => K.plug (.squiggle ℭ t l)

/-- A context is transparent when no squiggle lies between its hole and its root, so nothing in
it consumes the alternatives of the hole. -/
def Transparent : {α γ : Type} → Ctx α γ → Prop
  | _, _, hole => True
  | _, _, fn _ _ K => K.Transparent
  | _, _, arg _ _ K => K.Transparent
  | _, _, squiggle _ _ _ => False

/-- Through a transparent context the meaning of a constituent is the meaning of its hole bound
into the context, which is a continuation. -/
theorem meaning_plug {K : Ctx α γ} (hK : K.Transparent) (t : LF α) :
    (K.plug t).meaning = t.meaning >>= fun a ↦ (K.plug (lex a .bare)).meaning := by
  induction K with
  | hole => exact (bind_pure _).symm
  | fn x l K ih =>
    simp only [plug, ih hK (.app _ x l), meaning_eq_bind (.app _ x l), raw, label,
      meaning_lex_bare, seq_eq_bind_map, bind_assoc, pure_bind]
  | arg f l K ih =>
    simp only [plug, ih hK (.app f _ l), meaning_eq_bind (.app f _ l), raw, label,
      meaning_lex_bare]
    rw [WithAlternatives.seq_eq_bind_seq_pure f.meaning t.meaning, bind_assoc]
    simp only [bind_assoc]
  | squiggle ℭ l K ih => exact hK.elim

end Ctx

/-- (58) at any depth. A constituent containing a [FoC]-marked constituent with no squiggle between
them is Given only if its ordinary value ignores the FoCus. -/
theorem ord_plug_eq_of_given {K : Ctx α γ} (hK : K.Transparent) {t : LF α}
    (ht : t.label.mark = .focused) {c : γ} (h : (K.plug t).meaning.Given c) (v : α) :
    (K.plug (lex v .bare)).ord = c := by
  rw [Ctx.meaning_plug hK, meaning_eq_mark, ht] at h
  rw [← ordinary_meaning]
  exact WithAlternatives.ordinary_eq_of_given_mark_focused_bind (fun _ ↦ wellFormed_meaning _) h v

/-- (58) in the paper's form. A constituent whose ordinary value depends on a [FoC]-marked
constituent with no squiggle between them is not Given, so it cannot be [G]-marked. -/
theorem not_given_plug_foc {K : Ctx α γ} (hK : K.Transparent) {v w : α}
    (hvw : (K.plug (lex v .bare)).ord ≠ (K.plug (lex w .bare)).ord) {t : LF α}
    (ht : t.label.mark = .focused) (c : γ) : ¬ (K.plug t).meaning.Given c := fun h ↦
  hvw ((ord_plug_eq_of_given hK ht h v).trans (ord_plug_eq_of_given hK ht h w).symm)

/-- The dependence is needed, as the paper's derivation of (58) overlooks. *[Mary]FoC came or
didn't come* contains a FoCus that nothing consumes, yet it is Given with respect to the
tautology, since its predicate holds of everyone. -/
theorem given_foc_came_or_not {E W : Type} (came : E → Set W) (mary : E) :
    (app (lex (fun x ↦ came x ∪ (came x)ᶜ) .bare) (lex mary .foc) .bare).meaning.Given
      Set.univ := by
  refine Set.ext fun s ↦ ?_
  simp only [meaning, Label.bare, Label.foc, WithAlternatives.mark_unfeatured,
    WithAlternatives.mark_focused, WithAlternatives.mem_alternatives_seq,
    WithAlternatives.unfeatured_alternatives, WithAlternatives.unfeatured_ordinary,
    WithAlternatives.focused_alternatives, Set.mem_singleton_iff, Set.mem_univ, true_and,
    exists_eq_left, Set.union_compl_self]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨mary, h.symm⟩⟩

/-! ### Overfocusing (49)–(51)

Over the variants of a predication, every relabelling of its nodes, a narrow FoCus on one argument
represents a contrast with an antecedent differing there, and the FoCus on both arguments of (50b)
does not, since the narrow variant (51) has fewer alternatives that still include the
antecedent. -/

section Overfocusing

variable {σ τ : Type}

/-- The application `g z`, its function, argument and root labelled `l₁`, `l₂`, `l₃`. -/
def pred₁ (g : σ → τ) (z : σ) (l₁ : Label (σ → τ)) (l₂ : Label σ) (l₃ : Label τ) : LF τ :=
  app (lex g l₁) (lex z l₂) l₃

theorem isVariant_pred₁ (g : σ → τ) (z : σ) (l₁ l₁' : Label (σ → τ)) (l₂ l₂' : Label σ)
    (l₃ l₃' : Label τ) : IsVariant (pred₁ g z l₁ l₂ l₃) (pred₁ g z l₁' l₂' l₃') :=
  .app _ _ (.lex _ _ _) (.lex _ _ _)

theorem eq_pred₁_of_isVariant {g : σ → τ} {z : σ} {l₁ : Label (σ → τ)} {l₂ : Label σ}
    {l₃ : Label τ} {s : LF τ} (h : IsVariant s (pred₁ g z l₁ l₂ l₃)) :
    ∃ l₁' l₂' l₃', s = pred₁ g z l₁' l₂' l₃' := by
  cases h with
  | app l₃' _ hg hz =>
    cases hg with
    | lex _ l₁' _ => cases hz with
      | lex _ l₂' _ => exact ⟨l₁', l₂', l₃', rfl⟩

theorem alternatives_pred₁_eq_univ {g : σ → τ} {z : σ} {l₁ : Label (σ → τ)} {l₂ : Label σ}
    {l₃ : Label τ} (h : l₁.mark = .focused ∨ l₃.mark = .focused) :
    (pred₁ g z l₁ l₂ l₃).meaning.alternatives = Set.univ := by
  rcases l₃ with ⟨_ | _, _⟩
  · rcases h with h | h
    · simp only [pred₁, meaning, h, WithAlternatives.mark_unfeatured]
      exact WithAlternatives.alternatives_seq_eq_univ rfl ⟨_, (lex z l₂).wellFormed_meaning⟩
    · exact absurd h nofun
  · rfl

theorem alternatives_pred₁ {g : σ → τ} {z : σ} {l₁ : Label (σ → τ)} (l₂ : Label σ)
    {l₃ : Label τ} (h₁ : l₁.mark = .unfeatured) (h₃ : l₃.mark = .unfeatured) :
    (pred₁ g z l₁ l₂ l₃).meaning.alternatives = g '' (lex z l₂).meaning.alternatives := by
  simp only [pred₁, meaning, h₁, h₃, WithAlternatives.mark_unfeatured]
  ext c
  simp [WithAlternatives.mem_alternatives_seq]

theorem representsContrast_pred₁ {g : σ → τ} (hg : Function.Injective g) (z : σ) {z' : σ}
    (hz : z' ≠ z) : (pred₁ g z .bare .foc .bare).RepresentsContrast (g z') := by
  have ht : (pred₁ g z .bare .foc .bare).meaning.alternatives = Set.range g := by
    rw [alternatives_pred₁ _ rfl rfl]; simp [meaning, Label.foc]
  rw [representsContrast_iff, ht]
  refine ⟨⟨z', rfl⟩, fun h ↦ hz (hg h), fun s hs hss ↦ ?_⟩
  obtain ⟨l₁, l₂, l₃, rfl⟩ := eq_pred₁_of_isVariant hs
  by_cases hu : l₁.mark = .focused ∨ l₃.mark = .focused
  · exact absurd (Set.subset_univ _) (alternatives_pred₁_eq_univ hu ▸ hss).2
  · rw [not_or] at hu
    have h₁ : l₁.mark = .unfeatured := by cases h : l₁.mark <;> simp_all
    have h₃ : l₃.mark = .unfeatured := by cases h : l₃.mark <;> simp_all
    rw [alternatives_pred₁ l₂ h₁ h₃] at hss ⊢
    rcases l₂ with ⟨_ | _, _⟩
    · rintro ⟨_, rfl, h⟩
      exact hz (hg h).symm
    · exact absurd (by simp [meaning]) (ne_of_ssubset hss)

variable {α β γ : Type} {f : α → β → γ}

/-- The predication `f x y`, its nodes labelled from the function down to the root. -/
def pred₂ (f : α → β → γ) (x : α) (y : β) (l₁ : Label (α → β → γ)) (l₂ : Label α)
    (l₃ : Label (β → γ)) (l₄ : Label β) (l₅ : Label γ) : LF γ :=
  app (pred₁ f x l₁ l₂ l₃) (lex y l₄) l₅

theorem isVariant_pred₂ (f : α → β → γ) (x : α) (y : β) {l₁ l₁' : Label (α → β → γ)}
    {l₂ l₂' : Label α} {l₃ l₃' : Label (β → γ)} {l₄ l₄' : Label β} {l₅ l₅' : Label γ} :
    IsVariant (pred₂ f x y l₁ l₂ l₃ l₄ l₅) (pred₂ f x y l₁' l₂' l₃' l₄' l₅') :=
  .app _ _ (isVariant_pred₁ ..) (.lex _ _ _)

theorem eq_pred₂_of_isVariant {x : α} {y : β} {l₁ : Label (α → β → γ)} {l₂ : Label α}
    {l₃ : Label (β → γ)} {l₄ : Label β} {l₅ : Label γ} {s : LF γ}
    (h : IsVariant s (pred₂ f x y l₁ l₂ l₃ l₄ l₅)) :
    ∃ l₁' l₂' l₃' l₄' l₅', s = pred₂ f x y l₁' l₂' l₃' l₄' l₅' := by
  unfold pred₂ at h
  cases h with
  | app l₅' _ hfx hy =>
    obtain ⟨l₁', l₂', l₃', rfl⟩ := eq_pred₁_of_isVariant hfx
    cases hy with
    | lex _ l₄' _ => exact ⟨l₁', l₂', l₃', l₄', l₅', rfl⟩

theorem alternatives_pred₂_eq_univ {x : α} {y : β} {l₁ : Label (α → β → γ)} {l₂ : Label α}
    {l₃ : Label (β → γ)} {l₄ : Label β} {l₅ : Label γ}
    (h : l₁.mark = .focused ∨ l₃.mark = .focused ∨ l₅.mark = .focused) :
    (pred₂ f x y l₁ l₂ l₃ l₄ l₅).meaning.alternatives = Set.univ := by
  rcases l₅ with ⟨_ | _, _⟩
  · have h' : l₁.mark = .focused ∨ l₃.mark = .focused := by
      rcases h with h | h | h
      exacts [.inl h, .inr h, absurd h nofun]
    simp only [pred₂, meaning, WithAlternatives.mark_unfeatured]
    exact WithAlternatives.alternatives_seq_eq_univ (alternatives_pred₁_eq_univ h')
      ⟨_, (lex y l₄).wellFormed_meaning⟩
  · rfl

theorem alternatives_pred₂ {x : α} {y : β} {l₁ : Label (α → β → γ)} (l₂ : Label α)
    {l₃ : Label (β → γ)} (l₄ : Label β) {l₅ : Label γ} (h₁ : l₁.mark = .unfeatured)
    (h₃ : l₃.mark = .unfeatured) (h₅ : l₅.mark = .unfeatured) :
    (pred₂ f x y l₁ l₂ l₃ l₄ l₅).meaning.alternatives =
      Set.image2 f (lex x l₂).meaning.alternatives (lex y l₄).meaning.alternatives := by
  have := alternatives_pred₁ (g := f) (z := x) l₂ h₁ h₃
  simp only [pred₂, meaning, h₅, WithAlternatives.mark_unfeatured] at this ⊢
  ext c
  simp only [WithAlternatives.mem_alternatives_seq, this, Set.mem_image, Set.mem_image2]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

private theorem marks_of_not {l₁ : Label (α → β → γ)} {l₃ : Label (β → γ)} {l₅ : Label γ}
    (h : ¬ (l₁.mark = .focused ∨ l₃.mark = .focused ∨ l₅.mark = .focused)) :
    l₁.mark = .unfeatured ∧ l₃.mark = .unfeatured ∧ l₅.mark = .unfeatured := by
  rcases l₁ with ⟨_ | _, _⟩ <;> rcases l₃ with ⟨_ | _, _⟩ <;> rcases l₅ with ⟨_ | _, _⟩ <;>
    simp_all

/-- (51) *John picked strawberries at [Sandy's]FoC farm* represents a contrast with (50a) *John
picked strawberries at Mary's farm*: no variant with fewer alternatives evokes it. -/
theorem representsContrast_narrow (hf : Function.Injective2 f) (x : α) {y y' : β} (hy : y' ≠ y) :
    (pred₂ f x y .bare .bare .bare .foc .bare).RepresentsContrast (f x y') := by
  have ht : (pred₂ f x y .bare .bare .bare .foc .bare).meaning.alternatives =
      Set.image2 f {x} Set.univ := by
    rw [alternatives_pred₂ _ _ rfl rfl rfl]; rfl
  rw [representsContrast_iff, ht]
  refine ⟨⟨x, rfl, y', trivial, rfl⟩, fun h ↦ hy (hf h).2, fun s hs hss ↦ ?_⟩
  obtain ⟨l₁, l₂, l₃, l₄, l₅, rfl⟩ := eq_pred₂_of_isVariant hs
  by_cases hu : l₁.mark = .focused ∨ l₃.mark = .focused ∨ l₅.mark = .focused
  · exact absurd (Set.subset_univ _) (alternatives_pred₂_eq_univ hu ▸ hss).2
  obtain ⟨h₁, h₃, h₅⟩ := marks_of_not hu
  rw [alternatives_pred₂ l₂ l₄ h₁ h₃ h₅] at hss ⊢
  rcases l₂ with ⟨_ | _, _⟩ <;> rcases l₄ with ⟨_ | _, _⟩
  · rintro ⟨_, -, _, rfl, h⟩
    exact hy (hf h).2.symm
  · exact absurd (by rfl) (ne_of_ssubset hss)
  · rintro ⟨_, -, _, rfl, h⟩
    exact hy (hf h).2.symm
  · exact absurd (Set.image2_subset (Set.subset_univ _) subset_rfl) hss.2

/-- (50b) *John picked [strawberries]FoC at [Sandy's]FoC farm* does not represent a contrast with
(50a), since its variant (51) has strictly fewer alternatives and (50a) among them (49iii). -/
theorem not_representsContrast_overfocused [Nontrivial α] (hf : Function.Injective2 f) (x : α)
    (y y' : β) : ¬ (pred₂ f x y .bare .foc .bare .foc .bare).RepresentsContrast (f x y') := by
  intro h
  obtain ⟨x', hx'⟩ := exists_ne x
  refine (representsContrast_iff.1 h).2.2 (pred₂ f x y .bare .bare .bare .foc .bare)
    (isVariant_pred₂ f x y) ?_ ?_
  · rw [alternatives_pred₂ _ _ rfl rfl rfl, alternatives_pred₂ _ _ rfl rfl rfl]
    refine (Set.image2_subset (Set.subset_univ _) subset_rfl).ssubset_of_not_subset fun hsub ↦ ?_
    obtain ⟨_, rfl, _, -, h⟩ := hsub ⟨x', trivial, y, trivial, rfl⟩
    exact hx' (hf h).1.symm
  · rw [alternatives_pred₂ _ _ rfl rfl rfl]
    exact ⟨x, rfl, y', trivial, rfl⟩

/-- (51) under a squiggle whose antecedent (50a) the surrounding window supplies is felicitous. -/
theorem felicitous_squiggle_narrow (hf : Function.Injective2 f) (x : α) {y y' : β} (hy : y' ≠ y)
    (w : Window) (hw : f x y' ∈ w.surrounding γ) :
    (squiggle {f x y'} (pred₂ f x y .bare .bare .bare .foc .bare) .bare).Felicitous w := by
  refine ⟨?_, Set.singleton_subset_iff.2 hw, ?_, Label.licensed_bare w _⟩
  · simp [pred₂, pred₁, Felicitous]
  · rintro _ rfl
    exact representsContrast_narrow hf x hy

end Overfocusing

/-! ### Second-occurrence focus (60) -/

section SecondOccurrence

variable {E W : Type} (only : (E → Set W) → E → Set W) (quote : E → E → Set W) (faculty : E)

/-- The VP of (60), *only ~𝔞 [quote [the faculty]FoC]*, [G]-marked with referent `p`. -/
def sofVP (𝔞 p : E → Set W) : LF (E → Set W) :=
  app (lex only .bare) (squiggle {𝔞} (pred₁ quote faculty .bare .foc .bare) .bare)
    ⟨.unfeatured, some p⟩

/-- (60) The [G]-marked VP containing the second occurrence of *the faculty* is felicitous. Its
squiggle represents a contrast with an accommodated antecedent, quoting someone other than the
faculty (fn. 53), and consumes the FoCus, so the VP is Given with respect to the VP of the
preceding sentence. -/
theorem felicitous_sofVP (hq : Function.Injective quote) {other : E} (ho : other ≠ faculty)
    (w : Window) (hp : only (quote faculty) ∈ w.preceding _)
    (ha : quote other ∈ w.surrounding _) :
    (sofVP only quote faculty (quote other) (only (quote faculty))).Felicitous w := by
  refine ⟨Label.licensed_bare w _,
    ⟨by simp [pred₁, Felicitous], Set.singleton_subset_iff.2 ha, ?_, Label.licensed_bare w _⟩, ?_⟩
  · rintro _ rfl
    exact representsContrast_pred₁ hq faculty ho
  · intro p hp'
    obtain rfl := Option.mem_some_iff.1 hp'
    refine ⟨hp, Set.ext fun c ↦ ?_⟩
    simp [meaning, ord, pred₁, Label.bare, WithAlternatives.mem_alternatives_seq, eq_comm]

/-- Without the squiggle the [G] on the VP is not licensed when whom one quotes matters to the
VP, since the FoCus on *the faculty* then reaches it (58). -/
theorem not_felicitous_without_squiggle {v v' : E} (hvv : only (quote v) ≠ only (quote v'))
    (w : Window) (p : E → Set W) :
    ¬ (app (lex only .bare) (pred₁ quote faculty .bare .foc .bare)
      ⟨.unfeatured, some p⟩).Felicitous w := fun ⟨_, _, hl⟩ ↦
  not_given_plug_foc (K := .arg (lex quote .bare) .bare
    (.arg (lex only .bare) ⟨.unfeatured, some p⟩ .hole)) trivial (v := v) (w := v') hvv
    (t := lex faculty .foc) rfl p (hl p rfl).2

end SecondOccurrence

end LF


/-! ### A-Givenness (§3) -/

/-- [schwarzschild-1999]'s A-Givenness in alternatives semantics: a salient discourse
referent is among the alternatives. -/
def isAGiven {α : Type*} (m : WithAlternatives α) (referent : α) : Prop :=
  referent ∈ m.alternatives

theorem isAGiven_of_given {α : Type*} {m : WithAlternatives α} {referent : α}
    (h : m.Given referent) : isAGiven m referent := by
  rw [isAGiven, h]; rfl

theorem not_given_of_isAGiven :
    ∃ (m : WithAlternatives ℕ) (referent : ℕ), isAGiven m referent ∧ ¬ m.Given referent :=
  ⟨⟨1, {1, 2}⟩, 1, by simp [isAGiven], not_given_of_nontrivial (Set.nontrivial_pair (by decide)) 1⟩

/-- *Every `P` is a `Q`*, with the restrictor and the scope as properties. -/
def every {E W : Type*} (P Q : E → Set W) : Set W := {w | ∀ x, w ∈ P x → w ∈ Q x}

/-- Footnote 14 finds Schwarzschild's givenness, entailment of the existential F-closure, too easy
to satisfy, which A-Givenness is not. The F-closure of *Every [cat]F is a complainer*, that every
`P` is a complainer for some `P`, holds at every world, since every complainer is a complainer. -/
theorem sUnion_alternatives_every_focused {E W : Type} (cat complainer : E → Set W) :
    ⋃₀ ((every · complainer) <$>
      (pure cat : WithAlternatives (E → Set W)).mark .focused).alternatives = Set.univ := by
  rw [WithAlternatives.mark_focused, WithAlternatives.alternatives_map_focused]
  exact Set.eq_univ_of_forall fun _ ↦ ⟨_, ⟨complainer, rfl⟩, fun _ h ↦ h⟩

/-! ### Hausa (footnote 21)

The paper does not conclude with [hartmann-zimmermann-2007] that information focus is
realised both in situ and ex situ in Hausa, since accommodated contrasts were not controlled
for, and it notes the corpus tendency, most information focus in situ and most selective,
contrastive, and corrective focus ex situ. On its inventory mere newness is no focus, so the
rereading the footnote suggests, without stating it, is that ex situ realises [FoC] and in situ
is unmarked. -/

/-- The paper's inventory over the pragmatic uses of [hartmann-zimmermann-2007] marks the
contrastive family with [FoC] and leaves new information unfeatured. -/
def useMark : Focus.Use → Focus.Mark
  | .newInfo => .unfeatured
  | _ => .focused

/-- On the rereading of Hausa a focus is realised ex situ iff it bears [FoC]. -/
def KSHausaReading (u : HartmannZimmermann2007.FocusUtterance) : Prop :=
  u.cfg.strategy = .exSitu ↔ useMark u.pragType = .focused

instance (u : HartmannZimmermann2007.FocusUtterance) : Decidable (KSHausaReading u) :=
  inferInstanceAs (Decidable (_ ↔ _))

theorem hz_cells_violate_reading :
    ¬ KSHausaReading HartmannZimmermann2007.exSitu_newInfo ∧
      ¬ KSHausaReading HartmannZimmermann2007.inSitu_corrective := by
  decide

end KratzerSelkirk2020
