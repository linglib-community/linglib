/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Replay

/-!
# Licensing a derivation

A licensing of Merge gives each lexical item a state in a commutative magma with zero, `0` being
the failure of Merge, and the trace of a moved object a state that depends on the object's own
and on the number of the trace.
Over a derivation whose traces are numbered by its movers, a licensing [extends to a morphism of
magmas](##Minimalist.Licensing.hom), and the derivation is licensed, `Derivation.LicensedBy`, when
every stage is in its domain, the object under construction and every copy extracted from it. The
derived object alone does not show this: a moved item leaves a trace, so whether it was merged
before it was saturated shows only at the stages before it moved. A morphism of licensings
[commutes with their extensions](##Minimalist.Licensing.comp_hom), so [the finer licensing licenses
what the coarser one does](##Minimalist.Derivation.LicensedBy.of_hom).

## Implementation notes

* The bare trace and a trace numbered past the movers name no object and are read as `0`.
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

variable {β γ : Type*} [CommMagma β] [Zero β] [CommMagma γ] [Zero γ]

/-- A licensing of Merge into `β`: the state of a lexical item, and the state of the trace a moved
object leaves, given the number of the trace and the object's own state. -/
structure Licensing (β : Type*) where
  /-- The state of a lexical item. -/
  lex : LexicalItem.Token → β
  /-- The state of the trace with the given number, of a moved object in the given state. -/
  trace : ℕ → β → β

/-- The number of movers the traces of an object refer to, one more than its largest trace
number: merging takes the larger bound, so the objects below a bound are closed under Merge. -/
def SyntacticObject.traceBound : SyntacticObject (ι := ℕ) → ℕ :=
  FreeCommMagma.elim (Leaf.elim (fun _ ↦ 0) fun u ↦ u.elim 0 (· + 1)) (fun _ _ a b ↦ max a b)
    fun _ _ a b ↦ max_comm a b

@[simp] theorem SyntacticObject.traceBound_merge (l r : SyntacticObject (ι := ℕ)) :
    (merge l r).traceBound = max l.traceBound r.traceBound :=
  FreeCommMagma.elim_mul ..

namespace Licensing

variable (L : Licensing β) (L' : Licensing γ)

/-- The morphism a licensing gives once its numbered traces have states. -/
def eval (states : List β) : SyntacticObject (ι := ℕ) →ₙ* β :=
  FreeCommMagma.lift (Leaf.elim L.lex fun u ↦ (u.bind (states[·]?)).getD 0)

/-- The states of the traces of the objects moved, in order: each the trace of its object, read
with the traces of the objects moved before it. -/
def traceStates (movers : List (SyntacticObject (ι := ℕ))) : List β :=
  movers.foldl (fun states m ↦ states ++ [L.trace states.length (L.eval states m)]) []

/-- A licensing over a derivation: the morphism of magmas reading each lexical item by its state
and each numbered trace as the trace of the mover it numbers. -/
def hom (d : Derivation ℕ) : SyntacticObject (ι := ℕ) →ₙ* β :=
  L.eval (L.traceStates d.movedItems)

/-- The state of the trace numbered `i` is the licensing's trace `i` of some state. -/
theorem exists_eq_trace_of_getElem? {movers : List (SyntacticObject (ι := ℕ))} {i : ℕ} {x : β}
    (h : (L.traceStates movers)[i]? = some x) : ∃ y, x = L.trace i y := by
  suffices key : ∀ states : List β, (∀ i x, states[i]? = some x → ∃ y, x = L.trace i y) →
      ∀ i x, (movers.foldl (fun states m ↦ states ++ [L.trace states.length (L.eval states m)])
        states)[i]? = some x → ∃ y, x = L.trace i y from
    key [] (fun _ _ h ↦ by simp at h) i x h
  clear h
  induction movers with
  | nil => exact fun _ h ↦ h
  | cons m movers ih =>
    refine fun states hs ↦ ih _ fun i x hx ↦ ?_
    rcases Nat.lt_or_ge i states.length with hi | hi
    · exact hs i x (by rwa [List.getElem?_append_left hi] at hx)
    · rw [List.getElem?_append_right hi, List.getElem?_singleton] at hx
      split_ifs at hx with h0
      obtain rfl : i = states.length := by omega
      exact ⟨_, (Option.some.inj hx).symm⟩

/-- A licensing reads an object from the states of the traces below its bound. -/
theorem eval_congr {states states' : List β} {s : SyntacticObject (ι := ℕ)}
    (h : ∀ i < s.traceBound, states[i]? = states'[i]?) : L.eval states s = L.eval states' s := by
  induction s using SyntacticObject.ind with
  | leaf a => rfl
  | trace => rfl
  | traceOf i => exact congrArg (·.getD 0) (h i i.lt_succ_self)
  | merge l r ihl ihr =>
    rw [show merge l r = l * r from rfl, map_mul, map_mul,
      ihl fun i hi ↦ h i (by rw [traceBound_merge]; exact lt_max_of_lt_left hi),
      ihr fun i hi ↦ h i (by rw [traceBound_merge]; exact lt_max_of_lt_right hi)]

theorem length_traceStates (movers : List (SyntacticObject (ι := ℕ))) :
    (L.traceStates movers).length = movers.length := by
  suffices key : ∀ states : List β, (movers.foldl
      (fun states m ↦ states ++ [L.trace states.length (L.eval states m)]) states).length =
        states.length + movers.length from (key []).trans (zero_add _)
  induction movers with
  | nil => exact fun _ ↦ rfl
  | cons m movers ih => exact fun states ↦ by rw [List.foldl_cons, ih]; simp; omega

/-- The trace states of the first movers are the first trace states. -/
theorem traceStates_prefix {movers movers' : List (SyntacticObject (ι := ℕ))}
    (h : movers <+: movers') : L.traceStates movers <+: L.traceStates movers' := by
  obtain ⟨rest, rfl⟩ := h
  rw [show L.traceStates (movers ++ rest) = rest.foldl
    (fun states m ↦ states ++ [L.trace states.length (L.eval states m)]) (L.traceStates movers)
    from List.foldl_append ..]
  generalize L.traceStates movers = states
  induction rest generalizing states with
  | nil => exact List.prefix_rfl
  | cons m rest ih => exact (List.prefix_append _ _).trans (ih _)

/-- An object whose traces number only the first movers is read alike with the later ones. -/
theorem eval_traceStates_of_prefix {movers movers' : List (SyntacticObject (ι := ℕ))}
    (h : movers <+: movers') {s : SyntacticObject (ι := ℕ)} (hs : s.traceBound ≤ movers.length) :
    L.eval (L.traceStates movers) s = L.eval (L.traceStates movers') s :=
  L.eval_congr fun i hi ↦ by
    obtain ⟨rest, hrest⟩ := L.traceStates_prefix h
    rw [← hrest, List.getElem?_append_left (by rw [length_traceStates]; omega)]

variable {L L'} {π : β →ₙ* γ}

theorem comp_eval (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a) (states : List β) :
    π.comp (L.eval states) = L'.eval (states.map π) :=
  FreeCommMagma.hom_ext fun ℓ ↦ by
    rcases ℓ with a | _ | i
    · exact hlex a
    · exact h0
    · show π ((states[i]?).getD 0) = ((states.map π)[i]?).getD 0
      rw [List.getElem?_map]
      cases states[i]? <;> simp [h0]

theorem traceStates_map (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a)
    (htrace : ∀ i x, π (L.trace i x) = L'.trace i (π x))
    (movers : List (SyntacticObject (ι := ℕ))) :
    L'.traceStates movers = (L.traceStates movers).map π := by
  suffices h : ∀ states : List β,
      movers.foldl (fun states m ↦ states ++ [L'.trace states.length (L'.eval states m)])
          (states.map π) =
        (movers.foldl (fun states m ↦ states ++ [L.trace states.length (L.eval states m)])
          states).map π from
    h []
  induction movers with
  | nil => exact fun _ ↦ rfl
  | cons m movers ih =>
    intro states
    rw [List.foldl_cons, List.foldl_cons, ← ih, List.map_append, List.map_singleton, htrace,
      ← comp_eval h0 hlex, MulHom.comp_apply, List.length_map]

/-- A morphism of licensings, preserving zero, the states of lexical items and traces, commutes
with their extensions over a derivation. -/
theorem comp_hom (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a)
    (htrace : ∀ i x, π (L.trace i x) = L'.trace i (π x)) (d : Derivation ℕ) :
    π.comp (L.hom d) = L'.hom d := by
  rw [hom, hom, comp_eval h0 hlex, traceStates_map h0 hlex htrace]

variable (L) in
/-- A licensing reads the objects of a stage alike over the stage and over the whole
derivation. -/
theorem hom_take (d : Derivation ℕ) (n : ℕ) {s : SyntacticObject (ι := ℕ)}
    (hs : s.traceBound ≤ (d.take n).movedItems.length) : L.hom (d.take n) s = L.hom d s :=
  L.eval_traceStates_of_prefix ((List.take_prefix n d.steps).filterMap _) hs

end Licensing

namespace Derivation

variable (L : Licensing β) {L' : Licensing γ} {d : Derivation ℕ} {n : ℕ}

/-- `L` licenses stage `n` of `d`: the ordered configuration the replay reaches after `n` steps
is in its domain, the object and every copy on the stack. -/
def LicensedAt (d : Derivation ℕ) (n : ℕ) : Prop :=
  ∃ c ∈ (d.take n).replay? d.moverIndex,
    ∀ x ∈ c.current :: c.stack, L.hom d x.toSyntacticObject ≠ 0

instance [DecidableEq β] (d : Derivation ℕ) (n : ℕ) : Decidable (d.LicensedAt L n) :=
  inferInstanceAs (Decidable (∃ c ∈ (d.take n).replay? d.moverIndex, _))

/-- The stage licensing looks at is the derivation's own. -/
theorem LicensedAt.hom_stageAt_ne_zero (h : d.LicensedAt L n) :
    L.hom d (d.stageAt n d.moverIndex) ≠ 0 := by
  obtain ⟨c, hc, hall⟩ := h
  rw [stageAt, final, ← (d.take n).replay?_faithful hc, Cfg.map_current]
  exact hall c.current List.mem_cons_self

/-- `L` licenses `d` when it licenses every stage. -/
def LicensedBy (d : Derivation ℕ) : Prop := ∀ n ≤ d.length, d.LicensedAt L n

instance [DecidableEq β] (d : Derivation ℕ) : Decidable (d.LicensedBy L) :=
  inferInstanceAs (Decidable (∀ n ≤ d.length, _))

variable {L} {π : β →ₙ* γ}

/-- A licensing licenses the derivations that its image under a morphism of licensings licenses:
a coarser licensing's derivations are the finer one's. -/
theorem LicensedBy.of_hom (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a)
    (htrace : ∀ i x, π (L.trace i x) = L'.trace i (π x)) (h : d.LicensedBy L') :
    d.LicensedBy L :=
  fun n hn ↦ (h n hn).imp fun c ⟨hc, hall⟩ ↦ ⟨hc, fun x hx hx0 ↦ hall x hx <| by
    rw [← Licensing.comp_hom h0 hlex htrace, MulHom.comp_apply, hx0, h0]⟩

end Derivation

/-! ### Token labels

Under a licensing with heads, a derivation whose traces are numbered has a token-labelled form:
each numbered trace is labelled by the head the licensing gives its mover. -/

/-- The leaf with a numbered trace labelled by the head listed for it, bare where there is
none. -/
def SyntacticObject.Leaf.withTraceHeads (heads : List (Option LexicalItem.Token)) :
    Leaf LexicalItem.Token ℕ → Leaf LexicalItem.Token LexicalItem.Token
  | .lex a => .lex a
  | .trace => .trace
  | .traceOf i => heads[i]?.join.elim .trace .traceOf

/-- The object with each numbered trace labelled by the head listed for it. -/
def SyntacticObject.withTraceHeads (heads : List (Option LexicalItem.Token)) :
    SyntacticObject (ι := ℕ) →ₙ* SyntacticObject :=
  FreeCommMagma.map (Leaf.withTraceHeads heads)

/-- The planar object with each numbered trace labelled by the head listed for it. -/
def PlanarSyntacticObject.withTraceHeads (heads : List (Option LexicalItem.Token)) :
    PlanarSyntacticObject (ι := ℕ) →ₙ* PlanarSyntacticObject :=
  FreeMagma.map (Leaf.withTraceHeads heads)

/-- The step with each numbered trace labelled by the head listed for it. -/
def Step.withTraceHeads (heads : List (Option LexicalItem.Token)) : Step ℕ → Step
  | .em side item => .em side (item.withTraceHeads heads)
  | .im mover side => .im (mover.withTraceHeads heads) side
  | .extract mover => .extract (mover.withTraceHeads heads)
  | .remerge side => .remerge side

namespace Derivation

variable [Head β] (L : Licensing β)

/-- The heads a licensing gives the movers of a derivation, in order. -/
def traceHeads (d : Derivation ℕ) : List (Option LexicalItem.Token) :=
  d.movedItems.map fun m ↦ head (L.hom d m)

/-- The token-labelled form of a numbered derivation: each trace labelled by the head the
licensing gives its mover. -/
def withTraceHeads (d : Derivation ℕ) : Derivation :=
  ⟨d.initial.withTraceHeads (d.traceHeads L), d.steps.map (Step.withTraceHeads (d.traceHeads L))⟩

end Derivation

/-! ### Triggered Merge -/

/-- The state of the trace of an object: its head with nothing left to select. -/
def SelectionState.saturate : SelectionState → SelectionState
  | ⟨some (a, _)⟩ => .of a []
  | ⟨none⟩ => 0

/-- Triggered Merge as a licensing: an item with its selectors, a trace the saturated head of the
object moved. -/
def SelectionState.licensing : Licensing SelectionState :=
  ⟨fun tok ↦ .of tok tok.item.sel, fun _ ↦ .saturate⟩

end Minimalist
