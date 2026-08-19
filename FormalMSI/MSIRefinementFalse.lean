import FormalMSI.MSIProof

/-!
# The MSI implementation does *not* refine the sequential specification

This file shows that the refinement stated by
`FormalMSI.MSIProof.enough_star` + `FormalMSI.MSIProof.initial_phi` is
false for `n = 2`, and hence that `initial_phi` is unprovable for *any*
simulation relation `φ` validating `enough_star`.

## The bug

A cache in state `I` with a pending request can fire
`cache_msi_step_internal.upgrade_from_I_rq1` several times, because the
rule neither consumes the pending request nor records that a `rqS` was
already issued.  The parent answers every `rqS` it sees (provided it is
in state `S` with the right tag) with a `rsS` data response, while
tracking the child with a *single* `shared_state` bit.

So: cache 0 issues `rqS` for address 0 twice, the parent responds twice,
cache 0 consumes one response, is later invalidated (`rqIσ`), and the
parent duly marks `shared_state 0 := I` — while the *second* `rsS`
response is still sitting in cache 0's `queue_pc`.  The protocol now
believes nobody holds address 0, lets cache 1 obtain `M` and commit a
store, after which cache 0 consumes the stale `rsS`, silently re-enters
`S` with the old value, and serves a load from it.

## The trace

Chronologically (cache 0 = `i0`, cache 1 = `i1`, address `a = 0`,
`b = 1`):

* `e1` `i0`: `ld_rq 0 0`  — load request for address 0
* `e2` `i0`: `ld_rs 0 0`  — the load returns 0
* `e3` `i1`: `ld_rq 0 1`  — load request for address 1
* `e4` `i1`: `ld_rs 0 0`  — the load returns 0
* `e5` `i1`: `st_rq 1 0 1` — store 1 to address 0
* `e6` `i1`: `ld_rq 2 0`  — load request for address 0
* `e7` `i1`: `ld_rs 2 1`  — the load returns 1 (the store committed)
* `e8` `i0`: `ld_rq 1 0`  — load request for address 0
* `e9` `i0`: `ld_rs 1 0`  — **stale**: the load returns 0

The sequential specification cannot match this: once `e7` was observed,
`memory 0 = 1` for good (the store to address 0 is the only store in the
trace), so the read that must answer `e8`'s request can only return 1.
-/

namespace FormalMSI.MSIRefinementFalse

open FormalMSI.MSI
open FormalMSI.SequentionalMI
open FormalMSI.MSIProof

abbrev i0 : Fin 2 := 0
abbrev i1 : Fin 2 := 1

abbrev e1 : TaggedEvent 2 := .tag i0 (.ld_rq 0 0)
abbrev e2 : TaggedEvent 2 := .tag i0 (.ld_rs 0 0)
abbrev e3 : TaggedEvent 2 := .tag i1 (.ld_rq 0 1)
abbrev e4 : TaggedEvent 2 := .tag i1 (.ld_rs 0 0)
abbrev e5 : TaggedEvent 2 := .tag i1 (.st_rq 1 0 1)
abbrev e6 : TaggedEvent 2 := .tag i1 (.ld_rq 2 0)
abbrev e7 : TaggedEvent 2 := .tag i1 (.ld_rs 2 1)
abbrev e8 : TaggedEvent 2 := .tag i0 (.ld_rq 1 0)
abbrev e9 : TaggedEvent 2 := .tag i0 (.ld_rs 1 0)

/-- The offending trace, in `star_extend` order (most recent event first). -/
abbrev badTrace : List (TaggedEvent 2) := [e9, e8, e7, e6, e5, e4, e3, e2, e1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The MSI implementation produces `badTrace` from its initial state. -/
theorem msi_reaches :
    ∃ m, star_extend msi_step_external msi_step_internal
          (default : MSIState 2) badTrace m := by
  have h0 : star_extend msi_step_external msi_step_internal
      (default : MSIState 2) [] default := star_extend.refl _
  -- e1: cache 0 requests a load of address 0
  have h1 := star_extend.step_ext _ _ _ _ _ h0
    (msi_step_external.cache _ _ _ i0 (cache_msi_step.ld_rq _ 0))
  -- cache 0 issues rqS for address 0, three times
  have h2 := star_extend.step_int _ _ _ _ _ h1
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.upgrade_from_I_rq1 _ 0 0 [] rfl rfl))
  have h3 := star_extend.step_int _ _ _ _ _ h2
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.upgrade_from_I_rq1 _ 0 0 [] rfl rfl))
  have h4 := star_extend.step_int _ _ _ _ _ h3
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.upgrade_from_I_rq1 _ 0 0 [] rfl rfl))
  -- parent fetches address 0 from memory, moving to S
  have h5 := star_extend.step_int _ _ _ _ _ h4
    (msi_step_internal.parent_no_queue _ _ _ i0
      (parent_msi_step.upgrade_to_M_data_not_avilable_rq2 _ 0 0 i0 0 rfl rfl
        (fun _ => rfl)))
  -- parent grants S to cache 0 twice (once per duplicate rqS)
  have h6 := star_extend.step_int _ _ _ _ _ h5
    (msi_step_internal.parent_upd_queue _ _ _ i0
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ 0 0 i0 0 rfl rfl rfl))
  have h7 := star_extend.step_int _ _ _ _ _ h6
    (msi_step_internal.parent_upd_queue _ _ _ i0
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ 0 0 i0 0 rfl rfl rfl))
  -- cache 0 consumes the first grant, becomes S(0, 0); the second grant stays
  have h8 := star_extend.step_int _ _ _ _ _ h7
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.upgrade_from_I_rsS _ 0 0 0 0 rfl rfl))
  -- cache 0 commits the load
  have h9 := star_extend.step_int _ _ _ _ _ h8
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.ld_rq_data_available1 _ 0 0 [] rfl rfl rfl))
  -- e2: the load response (value 0) leaves cache 0
  have h10 := star_extend.step_ext _ _ _ _ _ h9
    (msi_step_external.cache _ _ _ i0 (cache_msi_step.ld_rs _ 0 0 [] rfl))
  -- e3: cache 1 requests a load of address 1
  have h11 := star_extend.step_ext _ _ _ _ _ h10
    (msi_step_external.cache _ _ _ i1 (cache_msi_step.ld_rq _ 1))
  -- cache 1 issues rqS for address 1
  have h12 := star_extend.step_int _ _ _ _ _ h11
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.upgrade_from_I_rq1 _ 1 0 [] rfl rfl))
  -- parent sees cache 1's rqS for a different address and (without
  -- consuming it) sends an invalidation rqIσ to cache 0
  have h13 := star_extend.step_int _ _ _ _ _ h12
    (msi_step_internal.parent_upd_queue _ _ _ i0
      (parent_msi_step.upgrade_to_M_invalid_all2 _ 0 1 i1 i0 0 rfl
        Nat.zero_ne_one rfl (by decide)))
  -- cache 0 obeys the invalidation: S → I, sends rsIσ; the stale rsS grant
  -- is still in its queue_pc
  have h14 := star_extend.step_int _ _ _ _ _ h13
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.downgrade_from_M_rs1 _ 1 0 rfl rfl))
  -- parent processes cache 0's rsIσ: shared_state 0 := I
  have h15 := star_extend.step_int _ _ _ _ _ h14
    (msi_step_internal.parent_upd_queue _ _ _ i0
      (parent_msi_step.downgrade_from_M_rq2 _ 0 0 i0 1 rfl rfl rfl))
  -- parent drops S(0) → I (safe: everyone believed invalid)
  have h16 := star_extend.step_int _ _ _ _ _ h15
    (msi_step_internal.parent_no_queue _ _ _ i1
      (parent_msi_step.dawngrade_safe_parent_rq2 _ 0 1 i1 0 rfl rfl
        Nat.zero_ne_one (by decide)))
  -- parent fetches address 1, moving to S(1)
  have h17 := star_extend.step_int _ _ _ _ _ h16
    (msi_step_internal.parent_no_queue _ _ _ i1
      (parent_msi_step.upgrade_to_M_data_not_avilable_rq2 _ 0 1 i1 0 rfl rfl
        (by decide)))
  -- parent grants S(1) to cache 1
  have h18 := star_extend.step_int _ _ _ _ _ h17
    (msi_step_internal.parent_upd_queue _ _ _ i1
      (parent_msi_step.upgrade_to_M_data_avilable_rq2 _ 0 1 i1 0 rfl rfl rfl))
  -- cache 1 consumes the grant, becomes S(1, 0), commits the load
  have h19 := star_extend.step_int _ _ _ _ _ h18
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.upgrade_from_I_rsS _ 1 0 0 0 rfl rfl))
  have h20 := star_extend.step_int _ _ _ _ _ h19
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.ld_rq_data_available1 _ 1 0 [] rfl rfl rfl))
  -- e4: cache 1's load of address 1 returns 0
  have h21 := star_extend.step_ext _ _ _ _ _ h20
    (msi_step_external.cache _ _ _ i1 (cache_msi_step.ld_rs _ 0 0 [] rfl))
  -- e5: cache 1 requests a store of 1 to address 0
  have h22 := star_extend.step_ext _ _ _ _ _ h21
    (msi_step_external.cache _ _ _ i1 (cache_msi_step.st_rq _ 0 1))
  -- cache 1 evicts its S(1) line (wrong tag), sends rsIσ, then issues rqM
  have h23 := star_extend.step_int _ _ _ _ _ h22
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.rq_data_not_available1 _ 0 1 []
        (Or.inr ⟨1, rfl⟩) rfl Nat.one_ne_zero))
  have h24 := star_extend.step_int _ _ _ _ _ h23
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.upgrade_from_I_rq _ 0 1 1 [] rfl rfl))
  -- parent processes cache 1's rsIσ: shared_state 1 := I
  have h25 := star_extend.step_int _ _ _ _ _ h24
    (msi_step_internal.parent_upd_queue _ _ _ i1
      (parent_msi_step.downgrade_from_M_rq2 _ 1 1 i1 0 rfl rfl rfl))
  -- parent drops S(1) → I, triggered by cache 0's leftover third rqS(0)
  have h26 := star_extend.step_int _ _ _ _ _ h25
    (msi_step_internal.parent_no_queue _ _ _ i0
      (parent_msi_step.dawngrade_safe_parent_rq2 _ 0 0 i0 0 rfl rfl
        Nat.one_ne_zero (by decide)))
  -- parent fetches address 0 (still 0 in memory), moving to M(0)
  have h27 := star_extend.step_int _ _ _ _ _ h26
    (msi_step_internal.parent_no_queue _ _ _ i1
      (parent_msi_step.upgrade_to_M_data_not_avilable_rq1 _ 1 0 i1 0 rfl rfl
        (by decide)))
  -- parent grants M(0) to cache 1: everyone (wrongly) believed invalid
  have h28 := star_extend.step_int _ _ _ _ _ h27
    (msi_step_internal.parent_upd_queue _ _ _ i1
      (parent_msi_step.upgrade_to_M_data_avilable_rq1 _ 1 0 i1 0 rfl rfl rfl
        (by decide)))
  -- cache 1 consumes the grant, becomes M(0, 0), commits the store: value 1
  have h29 := star_extend.step_int _ _ _ _ _ h28
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.upgrade_from_I_rs _ 0 1 0 0 rfl rfl))
  have h30 := star_extend.step_int _ _ _ _ _ h29
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.st_rq_M_state _ 0 1 1 [] rfl rfl rfl))
  -- e6: cache 1 requests a load of address 0
  have h31 := star_extend.step_ext _ _ _ _ _ h30
    (msi_step_external.cache _ _ _ i1 (cache_msi_step.ld_rq _ 0))
  -- cache 1 commits the load from its M(0, 1) line
  have h32 := star_extend.step_int _ _ _ _ _ h31
    (msi_step_internal.cache _ _ i1 _
      (cache_msi_step_internal.ld_rq_data_available _ 0 2 [] rfl rfl rfl))
  -- e7: cache 1's load of address 0 returns 1
  have h33 := star_extend.step_ext _ _ _ _ _ h32
    (msi_step_external.cache _ _ _ i1 (cache_msi_step.ld_rs _ 1 2 [] rfl))
  -- e8: cache 0 requests a load of address 0
  have h34 := star_extend.step_ext _ _ _ _ _ h33
    (msi_step_external.cache _ _ _ i0 (cache_msi_step.ld_rq _ 0))
  -- cache 0 consumes the STALE rsS(0, 0) grant, silently re-entering S(0, 0)
  have h35 := star_extend.step_int _ _ _ _ _ h34
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.upgrade_from_I_rsS _ 0 0 0 0 rfl rfl))
  -- cache 0 commits the load from the stale line
  have h36 := star_extend.step_int _ _ _ _ _ h35
    (msi_step_internal.cache _ _ i0 _
      (cache_msi_step_internal.ld_rq_data_available1 _ 0 1 [] rfl rfl rfl))
  -- e9: cache 0's load of address 0 returns the stale 0
  have h37 := star_extend.step_ext _ _ _ _ _ h36
    (msi_step_external.cache _ _ _ i0 (cache_msi_step.ld_rs _ 0 1 [] rfl))
  exact ⟨_, h37⟩

/-!
## The sequential specification cannot produce `badTrace`

We prove a trace invariant: after any run of the specification whose
observable trace is a prefix of `badTrace`, the state satisfies a
configuration predicate `C·`, and the full `badTrace` is unreachable.
The essential point: `e7` can only be answered once `memory 0 = 1`, the
store `st_rq 1 0 1` is the unique store of the whole trace, so from then
on `memory 0 = 1` stays, and the read answering `e8`'s request can only
produce `ld_rs 1 1`, never `e9 = ld_rs 1 0`.
-/

private theorem fin2 (i : Fin 2) : i = i0 ∨ i = i1 :=
  match i with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

@[local simp] private theorem upd_00 {α} (f : Fin 2 → α) (v : α) :
    upd f i0 v i0 = v := if_pos rfl
@[local simp] private theorem upd_01 {α} (f : Fin 2 → α) (v : α) :
    upd f i0 v i1 = f i1 := if_neg (by decide)
@[local simp] private theorem upd_10 {α} (f : Fin 2 → α) (v : α) :
    upd f i1 v i0 = f i0 := if_neg (by decide)
@[local simp] private theorem upd_11 {α} (f : Fin 2 → α) (v : α) :
    upd f i1 v i1 = v := if_pos rfl
@[local simp] private theorem upd_nat00 {α} (f : Nat → α) (v : α) :
    upd f 0 v 0 = v := if_pos rfl

/-- Both queues of cache `j` have exactly the given content. -/
def Cq (s : SeqState 2) (j : Fin 2) (q r : List Event) : Prop :=
  (s.extqueue j).rq = q ∧ (s.extqueue j).rs = r

/-- All queues empty (holds after `e2`, `e4` and initially). -/
def C0 (s : SeqState 2) : Prop := Cq s i0 [] [] ∧ Cq s i1 [] []

/-- After `e1`: cache 0's load request is pending or committed. -/
def C1 (s : SeqState 2) : Prop :=
  Cq s i1 [] [] ∧ (Cq s i0 [.ld_rq 0 0] [] ∨ ∃ v, Cq s i0 [] [.ld_rs 0 v])

/-- After `e3`: cache 1's load request is pending or committed. -/
def C3 (s : SeqState 2) : Prop :=
  Cq s i0 [] [] ∧ (Cq s i1 [.ld_rq 0 1] [] ∨ ∃ v, Cq s i1 [] [.ld_rs 0 v])

/-- After `e5`: cache 1's store is pending, or committed (then `memory 0 = 1`). -/
def C5 (s : SeqState 2) : Prop :=
  Cq s i0 [] [] ∧
    (Cq s i1 [.st_rq 1 0 1] [] ∨ (Cq s i1 [] [] ∧ s.memory 0 = 1))

/-- After `e6`: the store and then the load of cache 1 commit in order. -/
def C6 (s : SeqState 2) : Prop :=
  Cq s i0 [] [] ∧
    (Cq s i1 [.st_rq 1 0 1, .ld_rq 2 0] [] ∨
      (Cq s i1 [.ld_rq 2 0] [] ∧ s.memory 0 = 1) ∨
      (Cq s i1 [] [.ld_rs 2 1] ∧ s.memory 0 = 1))

/-- After `e7`: everything is drained and the store has surely committed. -/
def C7 (s : SeqState 2) : Prop := C0 s ∧ s.memory 0 = 1

/-- After `e8`: cache 0's load can only ever be answered by `ld_rs 1 1`. -/
def C8 (s : SeqState 2) : Prop :=
  Cq s i1 [] [] ∧ s.memory 0 = 1 ∧
    (Cq s i0 [.ld_rq 1 0] [] ∨ Cq s i0 [] [.ld_rs 1 1])

/-- The trace invariant: one configuration predicate per prefix of
`badTrace`, and `badTrace` itself is unreachable. -/
def traceInv (l : List (TaggedEvent 2)) (s : SeqState 2) : Prop :=
  (l = [] → C0 s) ∧
  (l = [e1] → C1 s) ∧
  (l = [e2, e1] → C0 s) ∧
  (l = [e3, e2, e1] → C3 s) ∧
  (l = [e4, e3, e2, e1] → C0 s) ∧
  (l = [e5, e4, e3, e2, e1] → C5 s) ∧
  (l = [e6, e5, e4, e3, e2, e1] → C6 s) ∧
  (l = [e7, e6, e5, e4, e3, e2, e1] → C7 s) ∧
  (l = [e8, e7, e6, e5, e4, e3, e2, e1] → C8 s) ∧
  (l = badTrace → False)

/-! ### Preservation by internal steps -/

/-- No internal step can fire when both request queues are empty. -/
private theorem no_int {s s' : SeqState 2} {ie}
    (h0 : (s.extqueue i0).rq = []) (h1 : (s.extqueue i1).rq = []) :
    ¬ seq_internal_step s ie s' := by
  intro h
  cases h with
  | read t a v i rst hrq hmem =>
    rcases fin2 i with rfl | rfl <;> simp_all
  | write t a v i rst hrq =>
    rcases fin2 i with rfl | rfl <;> simp_all

private theorem int1 {s s' : SeqState 2} {ie}
    (hc : C1 s) (h : seq_internal_step s ie s') : C1 s' := by
  obtain ⟨h1, hcfg⟩ := hc
  cases h with
  | read t a v i rst hrq hmem =>
    rcases fin2 i with rfl | rfl
    · rcases hcfg with hA | ⟨v', hB⟩
      · rw [hA.1] at hrq
        injection hrq with he hrst
        injection he with ht ha
        subst ht ha hrst
        exact ⟨by simp [Cq, h1.1, h1.2], Or.inr ⟨v, by simp [Cq, hA.2]⟩⟩
      · rw [hB.1] at hrq; exact absurd hrq (by simp)
    · rw [h1.1] at hrq; exact absurd hrq (by simp)
  | write t a v i rst hrq =>
    rcases fin2 i with rfl | rfl
    · rcases hcfg with hA | ⟨v', hB⟩
      · rw [hA.1] at hrq; simp at hrq
      · rw [hB.1] at hrq; exact absurd hrq (by simp)
    · rw [h1.1] at hrq; exact absurd hrq (by simp)

private theorem int3 {s s' : SeqState 2} {ie}
    (hc : C3 s) (h : seq_internal_step s ie s') : C3 s' := by
  obtain ⟨h0, hcfg⟩ := hc
  cases h with
  | read t a v i rst hrq hmem =>
    rcases fin2 i with rfl | rfl
    · rw [h0.1] at hrq; exact absurd hrq (by simp)
    · rcases hcfg with hA | ⟨v', hB⟩
      · rw [hA.1] at hrq
        injection hrq with he hrst
        injection he with ht ha
        subst ht ha hrst
        exact ⟨by simp [Cq, h0.1, h0.2], Or.inr ⟨v, by simp [Cq, hA.2]⟩⟩
      · rw [hB.1] at hrq; exact absurd hrq (by simp)
  | write t a v i rst hrq =>
    rcases fin2 i with rfl | rfl
    · rw [h0.1] at hrq; exact absurd hrq (by simp)
    · rcases hcfg with hA | ⟨v', hB⟩
      · rw [hA.1] at hrq; simp at hrq
      · rw [hB.1] at hrq; exact absurd hrq (by simp)

private theorem int5 {s s' : SeqState 2} {ie}
    (hc : C5 s) (h : seq_internal_step s ie s') : C5 s' := by
  obtain ⟨h0, hcfg⟩ := hc
  cases h with
  | read t a v i rst hrq hmem =>
    rcases fin2 i with rfl | rfl
    · rw [h0.1] at hrq; exact absurd hrq (by simp)
    · rcases hcfg with hA | hB
      · rw [hA.1] at hrq; simp at hrq
      · rw [hB.1.1] at hrq; exact absurd hrq (by simp)
  | write t a v i rst hrq =>
    rcases fin2 i with rfl | rfl
    · rw [h0.1] at hrq; exact absurd hrq (by simp)
    · rcases hcfg with hA | hB
      · rw [hA.1] at hrq
        injection hrq with he hrst
        injection he with ht ha hv
        subst ht ha hv hrst
        refine ⟨by simp [Cq, h0.1, h0.2], Or.inr ⟨by simp [Cq, hA.2], by simp⟩⟩
      · rw [hB.1.1] at hrq; exact absurd hrq (by simp)

private theorem int6 {s s' : SeqState 2} {ie}
    (hc : C6 s) (h : seq_internal_step s ie s') : C6 s' := by
  obtain ⟨h0, hcfg⟩ := hc
  cases h with
  | read t a v i rst hrq hmem =>
    rcases fin2 i with rfl | rfl
    · rw [h0.1] at hrq; exact absurd hrq (by simp)
    · rcases hcfg with hA | hB | hC
      · rw [hA.1] at hrq; simp at hrq
      · rw [hB.1.1] at hrq
        injection hrq with he hrst
        injection he with ht ha
        subst ht ha hrst
        subst hmem
        refine ⟨by simp [Cq, h0.1, h0.2],
          Or.inr (Or.inr ⟨by simp [Cq, hB.1.2, hB.2], by simp [hB.2]⟩)⟩
      · rw [hC.1.1] at hrq; exact absurd hrq (by simp)
  | write t a v i rst hrq =>
    rcases fin2 i with rfl | rfl
    · rw [h0.1] at hrq; exact absurd hrq (by simp)
    · rcases hcfg with hA | hB | hC
      · rw [hA.1] at hrq
        injection hrq with he hrst
        injection he with ht ha hv
        subst ht ha hv hrst
        refine ⟨by simp [Cq, h0.1, h0.2],
          Or.inr (Or.inl ⟨by simp [Cq, hA.2], by simp⟩)⟩
      · rw [hB.1.1] at hrq; simp at hrq
      · rw [hC.1.1] at hrq; exact absurd hrq (by simp)

private theorem int8 {s s' : SeqState 2} {ie}
    (hc : C8 s) (h : seq_internal_step s ie s') : C8 s' := by
  obtain ⟨h1, hmem0, hcfg⟩ := hc
  cases h with
  | read t a v i rst hrq hmem =>
    rcases fin2 i with rfl | rfl
    · rcases hcfg with hA | hB
      · rw [hA.1] at hrq
        injection hrq with he hrst
        injection he with ht ha
        subst ht ha hrst
        subst hmem
        refine ⟨by simp [Cq, h1.1, h1.2], by simp [hmem0],
          Or.inr ⟨by simp, by simp [hA.2, hmem0]⟩⟩
      · rw [hB.1] at hrq; exact absurd hrq (by simp)
    · rw [h1.1] at hrq; exact absurd hrq (by simp)
  | write t a v i rst hrq =>
    rcases fin2 i with rfl | rfl
    · rcases hcfg with hA | hB
      · rw [hA.1] at hrq; simp at hrq
      · rw [hB.1] at hrq; exact absurd hrq (by simp)
    · rw [h1.1] at hrq; exact absurd hrq (by simp)

/-! ### Preservation by external steps -/

private theorem ext1 {s s' : SeqState 2}
    (hc : C0 s) (h : seq_step s e1 s') : C1 s' := by
  generalize hE : (e1 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i =>
    injection hE with hi hev
    subst hi
    injection hev with ht ha
    subst ha
    exact ⟨by simp [Cq, hc.2.1, hc.2.2],
      Or.inl (by simp [Cq, hc.1.1, hc.1.2, ← ht])⟩
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs => simp at hE

private theorem ext2 {s s' : SeqState 2}
    (hc : C1 s) (h : seq_step s e2 s') : C0 s' := by
  obtain ⟨h1, hcfg⟩ := hc
  generalize hE : (e2 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i => simp at hE
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs =>
    injection hE with hi hev
    subst hi
    injection hev with ht hv
    subst ht; subst hv
    rcases hcfg with hA | ⟨v', hB⟩
    · rw [hA.2] at hrs; exact absurd hrs (by simp)
    · rw [hB.2] at hrs
      injection hrs with he hrst
      subst hrst
      exact ⟨⟨by simp [hB.1], by simp⟩,
        by simp [Cq, h1.1, h1.2]⟩

private theorem ext3 {s s' : SeqState 2}
    (hc : C0 s) (h : seq_step s e3 s') : C3 s' := by
  generalize hE : (e3 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i =>
    injection hE with hi hev
    subst hi
    injection hev with ht ha
    subst ha
    exact ⟨by simp [Cq, hc.1.1, hc.1.2],
      Or.inl (by simp [Cq, hc.2.1, hc.2.2, ← ht])⟩
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs => simp at hE

private theorem ext4 {s s' : SeqState 2}
    (hc : C3 s) (h : seq_step s e4 s') : C0 s' := by
  obtain ⟨h0, hcfg⟩ := hc
  generalize hE : (e4 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i => simp at hE
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs =>
    injection hE with hi hev
    subst hi
    injection hev with ht hv
    subst ht; subst hv
    rcases hcfg with hA | ⟨v', hB⟩
    · rw [hA.2] at hrs; exact absurd hrs (by simp)
    · rw [hB.2] at hrs
      injection hrs with he hrst
      subst hrst
      exact ⟨by simp [Cq, h0.1, h0.2],
        ⟨by simp [hB.1], by simp⟩⟩

private theorem ext5 {s s' : SeqState 2}
    (hc : C0 s) (h : seq_step s e5 s') : C5 s' := by
  generalize hE : (e5 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i => simp at hE
  | st_rq a v i =>
    injection hE with hi hev
    subst hi
    injection hev with ht ha hv
    subst ha; subst hv
    exact ⟨by simp [Cq, hc.1.1, hc.1.2],
      Or.inl (by simp [Cq, hc.2.1, hc.2.2, ← ht])⟩
  | ld_rs v t rst i hrs => simp at hE

private theorem ext6 {s s' : SeqState 2}
    (hc : C5 s) (h : seq_step s e6 s') : C6 s' := by
  obtain ⟨h0, hcfg⟩ := hc
  generalize hE : (e6 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i =>
    injection hE with hi hev
    subst hi
    injection hev with ht ha
    subst ha
    rcases hcfg with hA | hB
    · exact ⟨by simp [Cq, h0.1, h0.2],
        Or.inl (by simp [Cq, hA.1, hA.2, ← ht])⟩
    · exact ⟨by simp [Cq, h0.1, h0.2],
        Or.inr (Or.inl ⟨by simp [Cq, hB.1.1, hB.1.2, ← ht], by simp [hB.2]⟩)⟩
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs => simp at hE

private theorem ext7 {s s' : SeqState 2}
    (hc : C6 s) (h : seq_step s e7 s') : C7 s' := by
  obtain ⟨h0, hcfg⟩ := hc
  generalize hE : (e7 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i => simp at hE
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs =>
    injection hE with hi hev
    subst hi
    injection hev with ht hv
    subst ht; subst hv
    rcases hcfg with hA | hB | hC
    · rw [hA.2] at hrs; exact absurd hrs (by simp)
    · rw [hB.1.2] at hrs; exact absurd hrs (by simp)
    · rw [hC.1.2] at hrs
      injection hrs with he hrst
      subst hrst
      exact ⟨⟨by simp [Cq, h0.1, h0.2], ⟨by simp [hC.1.1], by simp⟩⟩,
        by simp [hC.2]⟩

private theorem ext8 {s s' : SeqState 2}
    (hc : C7 s) (h : seq_step s e8 s') : C8 s' := by
  obtain ⟨⟨h0, h1⟩, hmem⟩ := hc
  generalize hE : (e8 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i =>
    injection hE with hi hev
    subst hi
    injection hev with ht ha
    subst ha
    exact ⟨by simp [Cq, h1.1, h1.2], by simp [hmem],
      Or.inl (by simp [Cq, h0.1, h0.2, ← ht])⟩
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs => simp at hE

private theorem ext9 {s s' : SeqState 2}
    (hc : C8 s) (h : seq_step s e9 s') : False := by
  obtain ⟨h1, hmem, hcfg⟩ := hc
  generalize hE : (e9 : TaggedEvent 2) = ev at h
  cases h with
  | ld_rq a i => simp at hE
  | st_rq a v i => simp at hE
  | ld_rs v t rst i hrs =>
    injection hE with hi hev
    subst hi
    injection hev with ht hv
    subst ht; subst hv
    rcases hcfg with hA | hB
    · rw [hA.2] at hrs; exact absurd hrs (by simp)
    · rw [hB.2] at hrs
      injection hrs with he hrst
      injection he with ht' hv'
      exact absurd hv' (by simp)

/-! ### The invariant holds along every run of the specification -/

private theorem traceInv_default : traceInv [] (default : SeqState 2) := by
  unfold traceInv
  refine ⟨fun _ => ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact fun h => nomatch h

private theorem traceInv_int {l} {s s' : SeqState 2} {ie}
    (hr : traceInv l s) (h : seq_internal_step s ie s') : traceInv l s' := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hr
  unfold traceInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r9⟩
  · intro heq; exact absurd h (no_int ((r0 heq).1.1) ((r0 heq).2.1))
  · intro heq; exact int1 (r1 heq) h
  · intro heq; exact absurd h (no_int ((r2 heq).1.1) ((r2 heq).2.1))
  · intro heq; exact int3 (r3 heq) h
  · intro heq; exact absurd h (no_int ((r4 heq).1.1) ((r4 heq).2.1))
  · intro heq; exact int5 (r5 heq) h
  · intro heq; exact int6 (r6 heq) h
  · intro heq; exact absurd h (no_int ((r7 heq).1.1.1) ((r7 heq).1.2.1))
  · intro heq; exact int8 (r8 heq) h

private theorem traceInv_ext {l} {s s' : SeqState 2} {e}
    (hr : traceInv l s) (h : seq_step s e s') : traceInv (e :: l) s' := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, _⟩ := hr
  unfold traceInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun heq => nomatch heq
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext1 (r0 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext2 (r1 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext3 (r2 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext4 (r3 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext5 (r4 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext6 (r5 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext7 (r6 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext8 (r7 rfl) h
  · intro heq
    injection heq with he hl; subst he; subst hl
    exact ext9 (r8 rfl) h

private theorem seq_inv {s0 : SeqState 2} {l} {s : SeqState 2}
    (h : star_extend seq_step seq_internal_step s0 l s) :
    s0 = default → traceInv l s := by
  induction h with
  | refl =>
    intro h0; subst h0; exact traceInv_default
  | step_int l1 s1' s1'' ie hstar hint ih =>
    intro h0; exact traceInv_int (ih h0) hint
  | step_ext l1 s1' s1'' e hstar hext ih =>
    intro h0; exact traceInv_ext (ih h0) hext

/-- The sequential specification cannot produce `badTrace`. -/
theorem seq_cannot_match :
    ¬ ∃ s, star_extend seq_step seq_internal_step
            (default : SeqState 2) badTrace s := by
  rintro ⟨s, h⟩
  exact (seq_inv h rfl).2.2.2.2.2.2.2.2.2 rfl

/-!
## The no-go theorems
-/

/-- There is **no** simulation relation between the MSI implementation and
the sequential specification that relates the two initial states.  Hence
`FormalMSI.MSIProof.initial_phi` is unprovable for any definition of `φ`
that validates `FormalMSI.MSIProof.enough_star`. -/
theorem no_simulation_exists :
    ¬ ∃ R : MSIState 2 → SeqState 2 → Prop,
        simulation R ∧ R default default := by
  rintro ⟨R, hsim, hinit⟩
  obtain ⟨m, hstar⟩ := msi_reaches
  obtain ⟨s', hs', -⟩ := hsim _ _ _ _ hinit hstar
  exact seq_cannot_match ⟨s', hs'⟩

/-- In particular, `initial_phi` is false at `n = 2` for the greatest
simulation relation `φ` (for which `enough_star` holds). -/
theorem initial_phi_is_false : ¬ @φ 2 default default :=
  no_simulation_exists

/-- The general no-go statement, with `enough_star`'s statement spelled
out: no relation `ψ` can satisfy both `enough_star` and `initial_phi`. -/
theorem no_phi_works :
    ¬ ∃ ψ : MSIState 2 → SeqState 2 → Prop,
        (∀ (i i' : MSIState 2) (s : SeqState 2) (l : List (TaggedEvent 2)),
          ψ i s →
          star_extend msi_step_external msi_step_internal i l i' →
          ∃ s', star_extend seq_step seq_internal_step s l s' ∧ ψ i' s') ∧
        ψ default default :=
  fun ⟨ψ, hsim, hinit⟩ => no_simulation_exists ⟨ψ, hsim, hinit⟩

end FormalMSI.MSIRefinementFalse
