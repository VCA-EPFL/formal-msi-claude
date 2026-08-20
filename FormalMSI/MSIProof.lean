import FormalMSI.Star
import FormalMSI.MSI
import FormalMSI.SeqSpec
import Mathlib.Data.List.Basic

/-!
# Refinement of the sequential specification by the MSI protocol

States the simulation theorem `enough_star`: every behaviour of the MSI
implementation (`msi_step_external`/`msi_step_internal`) can be matched by
the sequential specification (`seq_step`/`seq_internal_step`), preserving
the simulation relation `φ`.  Here `φ` is defined as a concrete simulation
relation (`SimInv`), so `enough_star` follows from single-step simulation
lemmas by induction, and `initial_phi` holds by computation.
-/

namespace FormalMSI.MSIProof

open FormalMSI.MSI
open FormalMSI.SequentionalMI

/-!
## List helper lemmas
-/

theorem countP_eraseIdx {α} (p : α → Bool) {l : List α} {j : Nat} {x : α}
    (h : l[j]? = some x) :
    l.countP p = (l.eraseIdx j).countP p + (if p x then 1 else 0) := by
  induction l generalizing j with
  | nil => simp at h
  | cons a t ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [List.countP_cons]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.eraseIdx_cons_succ, List.countP_cons, ih h]
      omega

theorem mem_eraseIdx {α} {l : List α} {j : Nat} {x : α} (h : x ∈ l.eraseIdx j) : x ∈ l :=
  List.eraseIdx_subset h

theorem not_mem_of_countP_zero {α} {p : α → Bool} {l : List α} (h : l.countP p = 0)
    {x : α} (hx : x ∈ l) (hpx : p x = true) : False := by
  exact List.countP_eq_zero.mp h x hx hpx

/-!
## `upd` helper lemmas
-/

@[simp] theorem upd_self {α β : Type _} [DecidableEq α] (f : α → β) (x : α) (v : β) :
    upd f x v x = v := by simp [upd]

theorem upd_other {α β : Type _} [DecidableEq α] (f : α → β) (x y : α) (v : β) (h : ¬y = x) :
    upd f x v y = f y := by simp [upd, h]

/-!
## Message-kind predicates
-/

/-- Is the parent-to-child message an exclusive (`M`) data grant? -/
def isRsM : PCEvent → Bool
  | .rsM .. => true
  | _ => false

/-- Is the parent-to-child message a shared (`S`) data grant? -/
def isRsS : PCEvent → Bool
  | .rsS .. => true
  | _ => false

/-- Is the child-to-parent message a dirty write-back (leaving `M`)? -/
def isWbM : CPEvent → Bool
  | .rsIμ .. => true
  | _ => false

/-- Is the child-to-parent message a clean downgrade notification (leaving `S`)? -/
def isWbS : CPEvent → Bool
  | .rsIσ .. => true
  | _ => false

@[simp] theorem isRsM_rsM (t a v) : isRsM (.rsM t a v) = true := rfl
@[simp] theorem isRsM_rsS (t a v) : isRsM (.rsS t a v) = false := rfl
@[simp] theorem isRsM_rqIμ (t) : isRsM (.rqIμ t) = false := rfl
@[simp] theorem isRsM_rqIσ (t) : isRsM (.rqIσ t) = false := rfl
@[simp] theorem isRsS_rsS (t a v) : isRsS (.rsS t a v) = true := rfl
@[simp] theorem isRsS_rsM (t a v) : isRsS (.rsM t a v) = false := rfl
@[simp] theorem isRsS_rqIμ (t) : isRsS (.rqIμ t) = false := rfl
@[simp] theorem isRsS_rqIσ (t) : isRsS (.rqIσ t) = false := rfl
@[simp] theorem isWbM_rsIμ (t a v) : isWbM (.rsIμ t a v) = true := rfl
@[simp] theorem isWbM_rsIσ (t a) : isWbM (.rsIσ t a) = false := rfl
@[simp] theorem isWbM_rqS (t a) : isWbM (.rqS t a) = false := rfl
@[simp] theorem isWbM_rqM (t a) : isWbM (.rqM t a) = false := rfl
@[simp] theorem isWbS_rsIσ (t a) : isWbS (.rsIσ t a) = true := rfl
@[simp] theorem isWbS_rsIμ (t a v) : isWbS (.rsIμ t a v) = false := rfl
@[simp] theorem isWbS_rqS (t a) : isWbS (.rqS t a) = false := rfl
@[simp] theorem isWbS_rqM (t a) : isWbS (.rqM t a) = false := rfl

/-!
## The coherence tokens

For every cache `i` the protocol maintains a "permission token" discipline:
if the parent records `shared_state i = M` (resp. `S`) then exactly one of
the following holds — an unconsumed data grant is in flight to `i`, the
cache line of `i` actually holds the permission, or an unconsumed
write-back from `i` is in flight to the parent.  In every position the
token carries the current value of the specification memory at the
parent's tag.
-/

/-- Cache `i` holds no protocol permission and no data-bearing messages
are in flight to or from it. -/
def clean (c : CacheState) : Prop :=
  c.cache.mdata.state = Bstate.I ∧
  c.queue_pc.countP isRsM = 0 ∧
  c.queue_pc.countP isRsS = 0 ∧
  c.queue_cp.countP isWbM = 0 ∧
  c.queue_cp.countP isWbS = 0

/-- The `M` permission token for address `a` with current specification
value `v` is at cache `i` (in one of its three possible positions). -/
def mtoken (a : Addr) (v : Value) (c : CacheState) : Prop :=
  c.queue_pc.countP isRsM + (if c.cache.mdata.state = Bstate.M then 1 else 0) +
      c.queue_cp.countP isWbM = 1 ∧
  c.queue_pc.countP isRsS = 0 ∧
  c.queue_cp.countP isWbS = 0 ∧
  ¬c.cache.mdata.state = Bstate.S ∧
  (∀ t a' v', PCEvent.rsM t a' v' ∈ c.queue_pc → a' = a ∧ v' = v) ∧
  (c.cache.mdata.state = Bstate.M → c.cache.mdata.tag = a ∧ c.cache.value = v) ∧
  (∀ t a' v', CPEvent.rsIμ t a' v' ∈ c.queue_cp → a' = a ∧ v' = v)

/-- The `S` permission token for address `a` with current specification
value `v` is at cache `i`. -/
def stoken (a : Addr) (v : Value) (c : CacheState) : Prop :=
  c.queue_pc.countP isRsS + (if c.cache.mdata.state = Bstate.S then 1 else 0) +
      c.queue_cp.countP isWbS = 1 ∧
  c.queue_pc.countP isRsM = 0 ∧
  c.queue_cp.countP isWbM = 0 ∧
  ¬c.cache.mdata.state = Bstate.M ∧
  (∀ t a' v', PCEvent.rsS t a' v' ∈ c.queue_pc → a' = a ∧ v' = v) ∧
  (c.cache.mdata.state = Bstate.S → c.cache.mdata.tag = a ∧ c.cache.value = v) ∧
  (∀ t a', CPEvent.rsIσ t a' ∈ c.queue_cp → a' = a)

/-- Per-cache invariant while the parent line is in state `M`. -/
def mslot (a : Addr) (v : Value) (sh : Bstate) (c : CacheState) : Prop :=
  (sh = Bstate.M ∧ mtoken a v c) ∨ (sh = Bstate.I ∧ clean c)

/-- Per-cache invariant while the parent line is in state `S`. -/
def sslot (a : Addr) (v : Value) (sh : Bstate) (c : CacheState) : Prop :=
  (sh = Bstate.S ∧ stoken a v c) ∨ (sh = Bstate.I ∧ clean c)

/-!
## The simulation relation
-/

/-- The concrete simulation relation between an MSI implementation state
and a state of the sequential specification. -/
structure SimInv {n : Nat} (m : MSIState n) (s : SeqState n) : Prop where
  fresh_eq : ∀ i, (m.caches i).fresh_ident = s.fresh_ident i
  ext_eq : ∀ i, (m.caches i).extqueue = s.extqueue i
  conn : connections m.caches m.parent
  mem_eq : ∀ a, ¬(m.parent.parent.mdata.state = Bstate.M ∧ m.parent.parent.mdata.tag = a) →
      m.parent.memory a = s.memory a
  epochI : m.parent.parent.mdata.state = Bstate.I →
      ∀ i, m.parent.parent.mdata.shared_state i = Bstate.I ∧ clean (m.caches i)
  epochM_uniq : m.parent.parent.mdata.state = Bstate.M →
      ∀ i j, m.parent.parent.mdata.shared_state i = Bstate.M →
        m.parent.parent.mdata.shared_state j = Bstate.M → i = j
  epochM_slot : m.parent.parent.mdata.state = Bstate.M →
      ∀ i, mslot m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
        (m.parent.parent.mdata.shared_state i) (m.caches i)
  epochM_val : m.parent.parent.mdata.state = Bstate.M →
      (∀ i, m.parent.parent.mdata.shared_state i = Bstate.I) →
      m.parent.parent.value = s.memory m.parent.parent.mdata.tag
  epochS_val : m.parent.parent.mdata.state = Bstate.S →
      m.parent.parent.value = s.memory m.parent.parent.mdata.tag
  epochS_slot : m.parent.parent.mdata.state = Bstate.S →
      ∀ i, sslot m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
        (m.parent.parent.mdata.shared_state i) (m.caches i)

def φ {n : Nat} (i : MSIState n) (s : SeqState n) : Prop := SimInv i s

/-!
## Congruence and queue-extension lemmas for the tokens
-/

theorem bstate_eq_I {b : Bstate} (h1 : ¬b = Bstate.M) (h2 : ¬b = Bstate.S) : b = Bstate.I := by
  cases b <;> simp_all

theorem clean_congr {c c' : CacheState} (h1 : c'.cache = c.cache)
    (h2 : c'.queue_cp = c.queue_cp) (h3 : c'.queue_pc = c.queue_pc) (hc : clean c) :
    clean c' := by
  unfold clean at hc ⊢
  rw [h1, h2, h3]
  exact hc

theorem mtoken_congr {a v} {c c' : CacheState} (h1 : c'.cache = c.cache)
    (h2 : c'.queue_cp = c.queue_cp) (h3 : c'.queue_pc = c.queue_pc) (hc : mtoken a v c) :
    mtoken a v c' := by
  unfold mtoken at hc ⊢
  rw [h1, h2, h3]
  exact hc

theorem stoken_congr {a v} {c c' : CacheState} (h1 : c'.cache = c.cache)
    (h2 : c'.queue_cp = c.queue_cp) (h3 : c'.queue_pc = c.queue_pc) (hc : stoken a v c) :
    stoken a v c' := by
  unfold stoken at hc ⊢
  rw [h1, h2, h3]
  exact hc

/-- Appending a non-grant message to the parent-to-child queue preserves `clean`. -/
theorem clean_pc_append {c : CacheState} (hc : clean c) {e : PCEvent}
    (h1 : isRsM e = false) (h2 : isRsS e = false) :
    clean { c with queue_pc := c.queue_pc ++ [e] } := by
  obtain ⟨hst, hm, hs, hwm, hws⟩ := hc
  exact ⟨hst, by simp [List.countP_append, hm, h1], by simp [List.countP_append, hs, h2],
    hwm, hws⟩

theorem mtoken_pc_append {a v} {c : CacheState} (hc : mtoken a v c) {e : PCEvent}
    (h1 : isRsM e = false) (h2 : isRsS e = false) :
    mtoken a v { c with queue_pc := c.queue_pc ++ [e] } := by
  obtain ⟨hsum, hs, hws, hns, hmm, hcache, hmw⟩ := hc
  refine ⟨by simp [List.countP_append, h1]; omega, by simp [List.countP_append, hs, h2],
    hws, hns, ?_, hcache, hmw⟩
  intro t a' v' hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hmm t a' v' hmem
  · simp only [List.mem_singleton] at hmem
    subst hmem
    simp at h1

theorem stoken_pc_append {a v} {c : CacheState} (hc : stoken a v c) {e : PCEvent}
    (h1 : isRsM e = false) (h2 : isRsS e = false) :
    stoken a v { c with queue_pc := c.queue_pc ++ [e] } := by
  obtain ⟨hsum, hm, hwm, hns, hmm, hcache, hmw⟩ := hc
  refine ⟨by simp [List.countP_append, h2]; omega, by simp [List.countP_append, hm, h1],
    hwm, hns, ?_, hcache, hmw⟩
  intro t a' v' hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hmm t a' v' hmem
  · simp only [List.mem_singleton] at hmem
    subst hmem
    simp at h2

/-- Appending a non-writeback message to the child-to-parent queue preserves `clean`. -/
theorem clean_cp_append {c : CacheState} (hc : clean c) {e : CPEvent}
    (h1 : isWbM e = false) (h2 : isWbS e = false) :
    clean { c with queue_cp := c.queue_cp ++ [e] } := by
  obtain ⟨hst, hm, hs, hwm, hws⟩ := hc
  exact ⟨hst, hm, hs, by simp [List.countP_append, hwm, h1], by simp [List.countP_append, hws, h2]⟩

theorem mtoken_cp_append {a v} {c : CacheState} (hc : mtoken a v c) {e : CPEvent}
    (h1 : isWbM e = false) (h2 : isWbS e = false) :
    mtoken a v { c with queue_cp := c.queue_cp ++ [e] } := by
  obtain ⟨hsum, hs, hws, hns, hmm, hcache, hmw⟩ := hc
  refine ⟨by simp [List.countP_append, h1]; omega, hs, by simp [List.countP_append, hws, h2],
    hns, hmm, hcache, ?_⟩
  intro t a' v' hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hmw t a' v' hmem
  · simp only [List.mem_singleton] at hmem
    subst hmem
    simp at h1

theorem stoken_cp_append {a v} {c : CacheState} (hc : stoken a v c) {e : CPEvent}
    (h1 : isWbM e = false) (h2 : isWbS e = false) :
    stoken a v { c with queue_cp := c.queue_cp ++ [e] } := by
  obtain ⟨hsum, hm, hwm, hns, hmm, hcache, hmw⟩ := hc
  refine ⟨by simp [List.countP_append, h2]; omega, hm, by simp [List.countP_append, hwm, h1],
    hns, hmm, hcache, ?_⟩
  intro t a' hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hmw t a' hmem
  · simp only [List.mem_singleton] at hmem
    subst hmem
    simp at h2

/-!
## Classification lemmas

From the invariant, a cache line holding `M` (resp. `S`), or an in-flight
data grant or write-back, pins down the parent's epoch and the location of
the corresponding permission token.
-/

section Classify

variable {n : Nat} {m : MSIState n} {s : SeqState n}

theorem cst_M_facts (h : SimInv m s) (i : Fin n)
    (hM : (m.caches i).cache.mdata.state = Bstate.M) :
    m.parent.parent.mdata.state = Bstate.M ∧
    m.parent.parent.mdata.shared_state i = Bstate.M ∧
    mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) := by
  cases hp : m.parent.parent.mdata.state with
  | M =>
    rcases h.epochM_slot hp i with ⟨hsh, htok⟩ | ⟨_, hcl⟩
    · exact ⟨rfl, hsh, htok⟩
    · rw [hcl.1] at hM; cases hM
  | S =>
    rcases h.epochS_slot hp i with ⟨_, htok⟩ | ⟨_, hcl⟩
    · exact absurd hM htok.2.2.2.1
    · rw [hcl.1] at hM; cases hM
  | I =>
    rw [(h.epochI hp i).2.1] at hM; cases hM

theorem cst_S_facts (h : SimInv m s) (i : Fin n)
    (hS : (m.caches i).cache.mdata.state = Bstate.S) :
    m.parent.parent.mdata.state = Bstate.S ∧
    m.parent.parent.mdata.shared_state i = Bstate.S ∧
    stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) := by
  cases hp : m.parent.parent.mdata.state with
  | M =>
    rcases h.epochM_slot hp i with ⟨_, htok⟩ | ⟨_, hcl⟩
    · exact absurd hS htok.2.2.2.1
    · rw [hcl.1] at hS; cases hS
  | S =>
    rcases h.epochS_slot hp i with ⟨hsh, htok⟩ | ⟨_, hcl⟩
    · exact ⟨rfl, hsh, htok⟩
    · rw [hcl.1] at hS; cases hS
  | I =>
    rw [(h.epochI hp i).2.1] at hS; cases hS

theorem rsM_facts (h : SimInv m s) (i : Fin n) {t a v}
    (hmem : PCEvent.rsM t a v ∈ (m.caches i).queue_pc) :
    m.parent.parent.mdata.state = Bstate.M ∧
    m.parent.parent.mdata.shared_state i = Bstate.M ∧
    mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) ∧
    a = m.parent.parent.mdata.tag ∧ v = s.memory m.parent.parent.mdata.tag := by
  cases hp : m.parent.parent.mdata.state with
  | M =>
    rcases h.epochM_slot hp i with ⟨hsh, htok⟩ | ⟨_, hcl⟩
    · obtain ⟨ha, hv⟩ := htok.2.2.2.2.1 t a v hmem
      exact ⟨rfl, hsh, htok, ha, hv⟩
    · exact (not_mem_of_countP_zero hcl.2.1 hmem rfl).elim
  | S =>
    rcases h.epochS_slot hp i with ⟨_, htok⟩ | ⟨_, hcl⟩
    · exact (not_mem_of_countP_zero htok.2.1 hmem rfl).elim
    · exact (not_mem_of_countP_zero hcl.2.1 hmem rfl).elim
  | I =>
    exact (not_mem_of_countP_zero (h.epochI hp i).2.2.1 hmem rfl).elim

theorem rsS_facts (h : SimInv m s) (i : Fin n) {t a v}
    (hmem : PCEvent.rsS t a v ∈ (m.caches i).queue_pc) :
    m.parent.parent.mdata.state = Bstate.S ∧
    m.parent.parent.mdata.shared_state i = Bstate.S ∧
    stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) ∧
    a = m.parent.parent.mdata.tag ∧ v = s.memory m.parent.parent.mdata.tag := by
  cases hp : m.parent.parent.mdata.state with
  | M =>
    rcases h.epochM_slot hp i with ⟨_, htok⟩ | ⟨_, hcl⟩
    · exact (not_mem_of_countP_zero htok.2.1 hmem rfl).elim
    · exact (not_mem_of_countP_zero hcl.2.2.1 hmem rfl).elim
  | S =>
    rcases h.epochS_slot hp i with ⟨hsh, htok⟩ | ⟨_, hcl⟩
    · obtain ⟨ha, hv⟩ := htok.2.2.2.2.1 t a v hmem
      exact ⟨rfl, hsh, htok, ha, hv⟩
    · exact (not_mem_of_countP_zero hcl.2.2.1 hmem rfl).elim
  | I =>
    exact (not_mem_of_countP_zero (h.epochI hp i).2.2.2.1 hmem rfl).elim

theorem wbM_facts (h : SimInv m s) (i : Fin n) {t a v}
    (hmem : CPEvent.rsIμ t a v ∈ (m.caches i).queue_cp) :
    m.parent.parent.mdata.state = Bstate.M ∧
    m.parent.parent.mdata.shared_state i = Bstate.M ∧
    mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) ∧
    a = m.parent.parent.mdata.tag ∧ v = s.memory m.parent.parent.mdata.tag := by
  cases hp : m.parent.parent.mdata.state with
  | M =>
    rcases h.epochM_slot hp i with ⟨hsh, htok⟩ | ⟨_, hcl⟩
    · obtain ⟨ha, hv⟩ := htok.2.2.2.2.2.2 t a v hmem
      exact ⟨rfl, hsh, htok, ha, hv⟩
    · exact (not_mem_of_countP_zero hcl.2.2.2.1 hmem rfl).elim
  | S =>
    rcases h.epochS_slot hp i with ⟨_, htok⟩ | ⟨_, hcl⟩
    · exact (not_mem_of_countP_zero htok.2.2.1 hmem rfl).elim
    · exact (not_mem_of_countP_zero hcl.2.2.2.1 hmem rfl).elim
  | I =>
    exact (not_mem_of_countP_zero (h.epochI hp i).2.2.2.2.1 hmem rfl).elim

theorem wbS_facts (h : SimInv m s) (i : Fin n) {t a}
    (hmem : CPEvent.rsIσ t a ∈ (m.caches i).queue_cp) :
    m.parent.parent.mdata.state = Bstate.S ∧
    m.parent.parent.mdata.shared_state i = Bstate.S ∧
    stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) ∧
    a = m.parent.parent.mdata.tag := by
  cases hp : m.parent.parent.mdata.state with
  | M =>
    rcases h.epochM_slot hp i with ⟨_, htok⟩ | ⟨_, hcl⟩
    · exact (not_mem_of_countP_zero htok.2.2.1 hmem rfl).elim
    · exact (not_mem_of_countP_zero hcl.2.2.2.2 hmem rfl).elim
  | S =>
    rcases h.epochS_slot hp i with ⟨hsh, htok⟩ | ⟨_, hcl⟩
    · exact ⟨rfl, hsh, htok, htok.2.2.2.2.2.2 t a hmem⟩
    · exact (not_mem_of_countP_zero hcl.2.2.2.2 hmem rfl).elim
  | I =>
    exact (not_mem_of_countP_zero (h.epochI hp i).2.2.2.2.2 hmem rfl).elim

end Classify

/-!
## Cache-local update helper

An update that replaces cache `i` (mirroring the queue copies at the
parent) and possibly the interface part of the specification state at `i`
preserves the invariant, given that the tokens at `i` are preserved.
-/

theorem simInv_cache_local {n : Nat} {m : MSIState n} {s s' : SeqState n}
    (h : SimInv m s) {i : Fin n} {c' : CacheState}
    (hsm : s'.memory = s.memory)
    (hsf : ∀ j, ¬j = i → s'.fresh_ident j = s.fresh_ident j)
    (hse : ∀ j, ¬j = i → s'.extqueue j = s.extqueue j)
    (hfr : c'.fresh_ident = s'.fresh_ident i)
    (hex : c'.extqueue = s'.extqueue i)
    (hclean : clean (m.caches i) → clean c')
    (hmtok : m.parent.parent.mdata.state = Bstate.M →
        mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) →
        mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) c')
    (hstok : m.parent.parent.mdata.state = Bstate.S →
        stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) (m.caches i) →
        stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag) c') :
    SimInv
      { m with
          caches := upd m.caches i c',
          parent := { m.parent with
            queue_cip := upd m.parent.queue_cip i c'.queue_cp,
            queue_pci := upd m.parent.queue_pci i c'.queue_pc } } s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; simp [hfr]
    · simp [upd_other _ _ _ _ hj, h.fresh_eq j, hsf j hj]
  · intro j
    by_cases hj : j = i
    · subst hj; simp [hex]
    · simp [upd_other _ _ _ _ hj, h.ext_eq j, hse j hj]
  · intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp only [upd_other _ _ _ _ hj]
      exact h.conn j
  · intro a ha
    simp only at ha ⊢
    rw [hsm]
    exact h.mem_eq a ha
  · intro hp j
    simp only at hp ⊢
    refine ⟨(h.epochI hp j).1, ?_⟩
    by_cases hj : j = i
    · subst hj; simp only [upd_self]
      exact hclean (h.epochI hp j).2
    · simp only [upd_other _ _ _ _ hj]
      exact (h.epochI hp j).2
  · intro hp j k
    simp only at hp ⊢
    exact h.epochM_uniq hp j k
  · intro hp j
    simp only at hp ⊢
    rw [hsm]
    by_cases hj : j = i
    · subst hj; simp only [upd_self]
      rcases h.epochM_slot hp j with ⟨hsh, htok⟩ | ⟨hsh, hcl⟩
      · exact Or.inl ⟨hsh, hmtok hp htok⟩
      · exact Or.inr ⟨hsh, hclean hcl⟩
    · simp only [upd_other _ _ _ _ hj]
      exact h.epochM_slot hp j
  · intro hp hall
    simp only at hp hall ⊢
    rw [hsm]
    exact h.epochM_val hp hall
  · intro hp
    simp only at hp ⊢
    rw [hsm]
    exact h.epochS_val hp
  · intro hp j
    simp only at hp ⊢
    rw [hsm]
    by_cases hj : j = i
    · subst hj; simp only [upd_self]
      rcases h.epochS_slot hp j with ⟨hsh, htok⟩ | ⟨hsh, hcl⟩
      · exact Or.inl ⟨hsh, hstok hp htok⟩
      · exact Or.inr ⟨hsh, hclean hcl⟩
    · simp only [upd_other _ _ _ _ hj]
      exact h.epochS_slot hp j

/-!
## Single-step simulation lemmas
-/

theorem sim_external {n : Nat} {m m' : MSIState n} {s : SeqState n} {e : TaggedEvent n}
    (h : SimInv m s) (hs : msi_step_external m e m') :
    ∃ s', seq_step s e s' ∧ SimInv m' s' := by
  cases hs with
  | cache e cache' i hc =>
    cases hc with
    | ld_rq a =>
      refine ⟨{ s with
          fresh_ident := upd s.fresh_ident i (s.fresh_ident i).succ,
          extqueue := upd s.extqueue i
            { s.extqueue i with
                rq := (s.extqueue i).rq ++ [Event.ld_rq (s.fresh_ident i) a] } }, ?_, ?_⟩
      · rw [h.fresh_eq i]
        exact seq_step.ld_rq s a i
      · refine simInv_cache_local h rfl (fun j hj => upd_other _ _ _ _ hj)
          (fun j hj => upd_other _ _ _ _ hj) ?_ ?_
          (clean_congr rfl rfl rfl) (fun _ => mtoken_congr rfl rfl rfl)
          (fun _ => stoken_congr rfl rfl rfl)
        · simp [h.fresh_eq i]
        · simp [h.ext_eq i, h.fresh_eq i]
    | st_rq a v =>
      refine ⟨{ s with
          fresh_ident := upd s.fresh_ident i (s.fresh_ident i).succ,
          extqueue := upd s.extqueue i
            { s.extqueue i with
                rq := (s.extqueue i).rq ++ [Event.st_rq (s.fresh_ident i) a v] } }, ?_, ?_⟩
      · rw [h.fresh_eq i]
        exact seq_step.st_rq s a v i
      · refine simInv_cache_local h rfl (fun j hj => upd_other _ _ _ _ hj)
          (fun j hj => upd_other _ _ _ _ hj) ?_ ?_
          (clean_congr rfl rfl rfl) (fun _ => mtoken_congr rfl rfl rfl)
          (fun _ => stoken_congr rfl rfl rfl)
        · simp [h.fresh_eq i]
        · simp [h.ext_eq i, h.fresh_eq i]
    | ld_rs v t rst hrs =>
      refine ⟨{ s with
          extqueue := upd s.extqueue i { s.extqueue i with rs := rst } }, ?_, ?_⟩
      · refine seq_step.ld_rs s v t rst i ?_
        rw [← h.ext_eq i]
        exact hrs
      · refine simInv_cache_local h rfl (fun j hj => rfl)
          (fun j hj => upd_other _ _ _ _ hj) ?_ ?_
          (clean_congr rfl rfl rfl) (fun _ => mtoken_congr rfl rfl rfl)
          (fun _ => stoken_congr rfl rfl rfl)
        · simp [h.fresh_eq i]
        · simp [h.ext_eq i]

theorem sim_internal_cache {n : Nat} {m : MSIState n} {s : SeqState n} {i : Fin n}
    {e : CacheInternalEvent} {c' : CacheState}
    (h : SimInv m s) (hc : cache_msi_step_internal (m.caches i) e c') :
    ∃ s', star_extend seq_step seq_internal_step s [] s' ∧
      SimInv { m with
          caches := upd m.caches i c',
          parent := { m.parent with
            queue_cip := upd m.parent.queue_cip i c'.queue_cp,
            queue_pci := upd m.parent.queue_pci i c'.queue_pc } } s' := by
  cases hc with
  | ld_rq_data_available a t rst hrq hM htag =>
    obtain ⟨hpM, hsh, htok⟩ := cst_M_facts h i hM
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hM
    have ha : a = m.parent.parent.mdata.tag := htag.symm.trans hctag
    have hv : s.memory a = (m.caches i).cache.value := by rw [ha, hcval]
    have hrq' : (s.extqueue i).rq = Event.ld_rq t a :: rst := by
      rw [← h.ext_eq i]; exact hrq
    refine ⟨{ s with
        extqueue := upd s.extqueue i
          { s.extqueue i with
              rs := (s.extqueue i).rs ++ [Event.ld_rs t ((m.caches i).cache.value)],
              rq := rst } }, ?_, ?_⟩
    · exact .step_int _ _ _ _ _ (.refl s)
        (seq_internal_step.read s t a ((m.caches i).cache.value) i rst hrq' hv)
    · refine simInv_cache_local h rfl (fun j _ => rfl) (fun j hj => upd_other _ _ _ _ hj)
        ?_ ?_ (clean_congr rfl rfl rfl) (fun _ => mtoken_congr rfl rfl rfl)
        (fun _ => stoken_congr rfl rfl rfl)
      · simp [h.fresh_eq i]
      · simp [h.ext_eq i]
  | ld_rq_data_available1 a t rst hrq hS htag =>
    obtain ⟨hpS, hsh, htok⟩ := cst_S_facts h i hS
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hS
    have ha : a = m.parent.parent.mdata.tag := htag.symm.trans hctag
    have hv : s.memory a = (m.caches i).cache.value := by rw [ha, hcval]
    have hrq' : (s.extqueue i).rq = Event.ld_rq t a :: rst := by
      rw [← h.ext_eq i]; exact hrq
    refine ⟨{ s with
        extqueue := upd s.extqueue i
          { s.extqueue i with
              rs := (s.extqueue i).rs ++ [Event.ld_rs t ((m.caches i).cache.value)],
              rq := rst } }, ?_, ?_⟩
    · exact .step_int _ _ _ _ _ (.refl s)
        (seq_internal_step.read s t a ((m.caches i).cache.value) i rst hrq' hv)
    · refine simInv_cache_local h rfl (fun j _ => rfl) (fun j hj => upd_other _ _ _ _ hj)
        ?_ ?_ (clean_congr rfl rfl rfl) (fun _ => mtoken_congr rfl rfl rfl)
        (fun _ => stoken_congr rfl rfl rfl)
      · simp [h.fresh_eq i]
      · simp [h.ext_eq i]
  | st_rq_M_state a t v rst hrq hM htag =>
    obtain ⟨hpM, hsh, htok⟩ := cst_M_facts h i hM
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hM
    have ha : a = m.parent.parent.mdata.tag := htag.symm.trans hctag
    have hrq' : (s.extqueue i).rq = Event.st_rq t a v :: rst := by
      rw [← h.ext_eq i]; exact hrq
    have hsum := htok.1
    rw [if_pos hM] at hsum
    have hrsM : (m.caches i).queue_pc.countP isRsM = 0 := by omega
    have hwbM : (m.caches i).queue_cp.countP isWbM = 0 := by omega
    have hmv : upd s.memory a v (m.parent.parent.mdata.tag) = v := by
      rw [← ha, upd_self]
    refine ⟨{ s with
        extqueue := upd s.extqueue i { s.extqueue i with rq := rst },
        memory := upd s.memory a v }, ?_, ?_⟩
    · exact .step_int _ _ _ _ _ (.refl s) (seq_internal_step.write s t a v i rst hrq')
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst hj; simp [h.fresh_eq j]
        · simp [upd_other _ _ _ _ hj, h.fresh_eq j]
      · intro j
        by_cases hj : j = i
        · subst hj; simp [h.ext_eq j]
        · simp [upd_other _ _ _ _ hj, h.ext_eq j]
      · intro j
        by_cases hj : j = i
        · subst hj; simp
        · simp only [upd_other _ _ _ _ hj]
          exact h.conn j
      · intro b hb
        have hba : ¬b = a := fun hh => hb ⟨hpM, ha.symm.trans hh.symm⟩
        show m.parent.memory b = upd s.memory a v b
        rw [upd_other _ _ _ _ hba]
        exact h.mem_eq b hb
      · intro hp
        exact absurd (hpM.symm.trans hp) (by decide)
      · intro _ j k hj hk
        exact h.epochM_uniq hpM j k hj hk
      · intro _ j
        by_cases hj : j = i
        · subst hj
          simp only [upd_self]
          refine Or.inl ⟨hsh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hrsM, hwbM, hM]
          · exact htok.2.1
          · exact htok.2.2.1
          · exact htok.2.2.2.1
          · intro t' a' v' hmem
            exact (not_mem_of_countP_zero hrsM hmem rfl).elim
          · intro _
            exact ⟨htag.trans ha, hmv.symm⟩
          · intro t' a' v' hmem
            exact (not_mem_of_countP_zero hwbM hmem rfl).elim
        · rcases h.epochM_slot hpM j with ⟨hshj, _⟩ | ⟨hshj, hclj⟩
          · exact absurd (h.epochM_uniq hpM j i hshj hsh) hj
          · refine Or.inr ⟨hshj, ?_⟩
            show clean (upd m.caches i _ j)
            rw [upd_other _ _ _ _ hj]
            exact hclj
      · intro _ hall
        exact absurd (hall i) (by simp [hsh])
      · intro hp
        exact absurd (hpM.symm.trans hp) (by decide)
      · intro hp
        exact absurd (hpM.symm.trans hp) (by decide)
  | rq_data_not_available a t rst hrq hM hntag =>
    obtain ⟨hpM, hsh, htok⟩ := cst_M_facts h i hM
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hM
    have hsum := htok.1
    rw [if_pos hM] at hsum
    have hrsM : (m.caches i).queue_pc.countP isRsM = 0 := by omega
    have hwbM : (m.caches i).queue_cp.countP isWbM = 0 := by omega
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j _ => rfl) (fun j _ => rfl) ?_ ?_ ?_ ?_ ?_
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
    · intro hcl
      exact absurd (hcl.1.symm.trans hM) (by decide)
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.countP_append, hrsM, hwbM]
      · exact htok.2.1
      · simp [List.countP_append, htok.2.2.1]
      · simp
      · exact htok.2.2.2.2.1
      · intro hc'
        simp at hc'
      · intro t' a' v' hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact (not_mem_of_countP_zero hwbM hmem rfl).elim
        · simp only [List.mem_singleton, CPEvent.rsIμ.injEq] at hmem
          exact ⟨hmem.2.1.trans hctag, hmem.2.2.trans hcval⟩
    · intro _ htokS
      exact absurd hM htokS.2.2.2.1
  | rq_data_not_available1 a t rst hrq hS hntag =>
    obtain ⟨hpS, hsh, htok⟩ := cst_S_facts h i hS
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hS
    have hsum := htok.1
    rw [if_pos hS] at hsum
    have hrsS : (m.caches i).queue_pc.countP isRsS = 0 := by omega
    have hwbS : (m.caches i).queue_cp.countP isWbS = 0 := by omega
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j _ => rfl) (fun j _ => rfl) ?_ ?_ ?_ ?_ ?_
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
    · intro hcl
      exact absurd (hcl.1.symm.trans hS) (by decide)
    · intro hp _
      exact absurd (hpS.symm.trans hp) (by decide)
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.countP_append, hrsS, hwbS]
      · exact htok.2.1
      · simp [List.countP_append, htok.2.2.1]
      · simp
      · exact htok.2.2.2.2.1
      · intro hc'
        simp at hc'
      · intro t' a' hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact (not_mem_of_countP_zero hwbS hmem rfl).elim
        · simp only [List.mem_singleton, CPEvent.rsIσ.injEq] at hmem
          exact hmem.2.trans hctag
  | upgrade_from_I_rq a t v rst hrq hI =>
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j _ => rfl) (fun j _ => rfl) ?_ ?_
      (fun hcl => clean_cp_append hcl rfl rfl)
      (fun _ htok => mtoken_cp_append htok rfl rfl)
      (fun _ htok => stoken_cp_append htok rfl rfl)
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
  | upgrade_from_I_rq1 a t rst hrq hI =>
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j _ => rfl) (fun j _ => rfl) ?_ ?_
      (fun hcl => clean_cp_append hcl rfl rfl)
      (fun _ htok => mtoken_cp_append htok rfl rfl)
      (fun _ htok => stoken_cp_append htok rfl rfl)
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
  | upgrade_from_I_rs a t v j hj hI =>
    have hmemM : PCEvent.rsM t a v ∈ (m.caches i).queue_pc := List.mem_of_getElem? hj
    obtain ⟨hpM, hsh, htok, ha, hv⟩ := rsM_facts h i hmemM
    have hcntM := countP_eraseIdx isRsM hj
    have hcntS := countP_eraseIdx isRsS hj
    simp at hcntM hcntS
    have hsum := htok.1
    rw [if_neg (by simp [hI])] at hsum
    have herased : ((m.caches i).queue_pc.eraseIdx j).countP isRsM = 0 := by omega
    have hwbM : (m.caches i).queue_cp.countP isWbM = 0 := by omega
    have hrsS0 : ((m.caches i).queue_pc.eraseIdx j).countP isRsS = 0 := by
      have := htok.2.1; omega
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j' _ => rfl) (fun j' _ => rfl) ?_ ?_ ?_ ?_ ?_
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
    · intro hcl
      have := hcl.2.1
      omega
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [herased, hwbM]
      · exact hrsS0
      · exact htok.2.2.1
      · simp
      · intro t' a' v' hmem
        exact htok.2.2.2.2.1 t' a' v' (mem_eraseIdx hmem)
      · intro _
        exact ⟨ha, hv⟩
      · exact htok.2.2.2.2.2.2
    · intro hp _
      exact absurd (hpM.symm.trans hp) (by decide)
  | upgrade_from_I_rsS a t v j hj hI =>
    have hmemS : PCEvent.rsS t a v ∈ (m.caches i).queue_pc := List.mem_of_getElem? hj
    obtain ⟨hpS, hsh, htok, ha, hv⟩ := rsS_facts h i hmemS
    have hcntM := countP_eraseIdx isRsM hj
    have hcntS := countP_eraseIdx isRsS hj
    simp at hcntM hcntS
    have hsum := htok.1
    rw [if_neg (by simp [hI])] at hsum
    have herased : ((m.caches i).queue_pc.eraseIdx j).countP isRsS = 0 := by omega
    have hwbS : (m.caches i).queue_cp.countP isWbS = 0 := by omega
    have hrsM0 : ((m.caches i).queue_pc.eraseIdx j).countP isRsM = 0 := by
      have := htok.2.1; omega
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j' _ => rfl) (fun j' _ => rfl) ?_ ?_ ?_ ?_ ?_
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
    · intro hcl
      have := hcl.2.2.1
      omega
    · intro hp _
      exact absurd (hpS.symm.trans hp) (by decide)
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [herased, hwbS]
      · exact hrsM0
      · exact htok.2.2.1
      · simp
      · intro t' a' v' hmem
        exact htok.2.2.2.2.1 t' a' v' (mem_eraseIdx hmem)
      · intro _
        exact ⟨ha, hv⟩
      · exact htok.2.2.2.2.2.2
  | downgrade_from_M_rs j t hj hM =>
    obtain ⟨hpM, hsh, htok⟩ := cst_M_facts h i hM
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hM
    have hsum := htok.1
    rw [if_pos hM] at hsum
    have hrsM : (m.caches i).queue_pc.countP isRsM = 0 := by omega
    have hwbM : (m.caches i).queue_cp.countP isWbM = 0 := by omega
    have hcntM := countP_eraseIdx isRsM hj
    have hcntS := countP_eraseIdx isRsS hj
    simp at hcntM hcntS
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j' _ => rfl) (fun j' _ => rfl) ?_ ?_ ?_ ?_ ?_
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
    · intro hcl
      exact absurd (hcl.1.symm.trans hM) (by decide)
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h1 : ((m.caches i).queue_pc.eraseIdx j).countP isRsM = 0 := by omega
        simp [List.countP_append, h1, hwbM]
      · have h1 : ((m.caches i).queue_pc.eraseIdx j).countP isRsS = 0 := by
          have := htok.2.1
          omega
        exact h1
      · simp [List.countP_append, htok.2.2.1]
      · simp
      · intro t' a' v' hmem
        exact htok.2.2.2.2.1 t' a' v' (mem_eraseIdx hmem)
      · intro hc'
        simp at hc'
      · intro t' a' v' hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact (not_mem_of_countP_zero hwbM hmem rfl).elim
        · simp only [List.mem_singleton, CPEvent.rsIμ.injEq] at hmem
          exact ⟨hmem.2.1.trans hctag, hmem.2.2.trans hcval⟩
    · intro hp _
      exact absurd (hpM.symm.trans hp) (by decide)
  | downgrade_from_M_rs1 j t hj hS =>
    obtain ⟨hpS, hsh, htok⟩ := cst_S_facts h i hS
    obtain ⟨hctag, hcval⟩ := htok.2.2.2.2.2.1 hS
    have hsum := htok.1
    rw [if_pos hS] at hsum
    have hrsS : (m.caches i).queue_pc.countP isRsS = 0 := by omega
    have hwbS : (m.caches i).queue_cp.countP isWbS = 0 := by omega
    have hcntM := countP_eraseIdx isRsM hj
    have hcntS := countP_eraseIdx isRsS hj
    simp at hcntM hcntS
    refine ⟨s, .refl s, ?_⟩
    refine simInv_cache_local h rfl (fun j' _ => rfl) (fun j' _ => rfl) ?_ ?_ ?_ ?_ ?_
    · simp [h.fresh_eq i]
    · simp [h.ext_eq i]
    · intro hcl
      exact absurd (hcl.1.symm.trans hS) (by decide)
    · intro hp _
      exact absurd (hpS.symm.trans hp) (by decide)
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h1 : ((m.caches i).queue_pc.eraseIdx j).countP isRsS = 0 := by omega
        simp [List.countP_append, h1, hwbS]
      · have h1 : ((m.caches i).queue_pc.eraseIdx j).countP isRsM = 0 := by
          have := htok.2.1
          omega
        exact h1
      · simp [List.countP_append, htok.2.2.1]
      · simp
      · intro t' a' v' hmem
        exact htok.2.2.2.2.1 t' a' v' (mem_eraseIdx hmem)
      · intro hc'
        simp at hc'
      · intro t' a' hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact (not_mem_of_countP_zero hwbS hmem rfl).elim
        · simp only [List.mem_singleton, CPEvent.rsIσ.injEq] at hmem
          exact hmem.2.trans hctag

/-- The parent pushing a (non-grant) invalidation request to cache `i`
preserves the invariant. -/
theorem simInv_parent_push {n : Nat} {m : MSIState n} {s : SeqState n} (h : SimInv m s)
    (i : Fin n) (e : PCEvent) (h1 : isRsM e = false) (h2 : isRsS e = false) :
    SimInv { m with
        caches := upd m.caches i
          { m.caches i with
              queue_cp := m.parent.queue_cip i,
              queue_pc := m.parent.queue_pci i ++ [e] },
        parent := { m.parent with
          queue_pci := upd m.parent.queue_pci i (m.parent.queue_pci i ++ [e]) } } s := by
  have hcq := (h.conn i).1
  have hpq := (h.conn i).2
  have hpc : ∀ c : CacheState,
      c = { m.caches i with
              queue_cp := m.parent.queue_cip i,
              queue_pc := m.parent.queue_pci i ++ [e] } →
      c.cache = (m.caches i).cache ∧ c.queue_cp = (m.caches i).queue_cp ∧
        c.queue_pc = (m.caches i).queue_pc ++ [e] := by
    rintro c rfl
    exact ⟨rfl, hcq.symm, by rw [hpq]⟩
  obtain ⟨he1, he2, he3⟩ := hpc _ rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; simp [h.fresh_eq j]
    · simp [upd_other _ _ _ _ hj, h.fresh_eq j]
  · intro j
    by_cases hj : j = i
    · subst hj; simp [h.ext_eq j]
    · simp [upd_other _ _ _ _ hj, h.ext_eq j]
  · intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp only [upd_other _ _ _ _ hj]
      exact h.conn j
  · intro b hb
    exact h.mem_eq b hb
  · intro hp j
    refine ⟨(h.epochI hp j).1, ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [upd_self]
      exact clean_congr (c := { m.caches j with queue_pc := (m.caches j).queue_pc ++ [e] })
        he1 he2 he3 (clean_pc_append (h.epochI hp j).2 h1 h2)
    · simp only [upd_other _ _ _ _ hj]
      exact (h.epochI hp j).2
  · intro hp j k hj hk
    exact h.epochM_uniq hp j k hj hk
  · intro hp j
    by_cases hj : j = i
    · subst hj
      simp only [upd_self]
      rcases h.epochM_slot hp j with ⟨hsh, htok⟩ | ⟨hsh, hcl⟩
      · exact Or.inl ⟨hsh, mtoken_congr
          (c := { m.caches j with queue_pc := (m.caches j).queue_pc ++ [e] })
          he1 he2 he3 (mtoken_pc_append htok h1 h2)⟩
      · exact Or.inr ⟨hsh, clean_congr
          (c := { m.caches j with queue_pc := (m.caches j).queue_pc ++ [e] })
          he1 he2 he3 (clean_pc_append hcl h1 h2)⟩
    · simp only [upd_other _ _ _ _ hj]
      exact h.epochM_slot hp j
  · intro hp hall
    exact h.epochM_val hp hall
  · intro hp
    exact h.epochS_val hp
  · intro hp j
    by_cases hj : j = i
    · subst hj
      simp only [upd_self]
      rcases h.epochS_slot hp j with ⟨hsh, htok⟩ | ⟨hsh, hcl⟩
      · exact Or.inl ⟨hsh, stoken_congr
          (c := { m.caches j with queue_pc := (m.caches j).queue_pc ++ [e] })
          he1 he2 he3 (stoken_pc_append htok h1 h2)⟩
      · exact Or.inr ⟨hsh, clean_congr
          (c := { m.caches j with queue_pc := (m.caches j).queue_pc ++ [e] })
          he1 he2 he3 (clean_pc_append hcl h1 h2)⟩
    · simp only [upd_other _ _ _ _ hj]
      exact h.epochS_slot hp j

theorem sim_parent_no {n : Nat} {m : MSIState n} {s : SeqState n} {p' : ParentState n}
    {e : ParentEvent n} {i : Fin n}
    (h : SimInv m s) (hp : parent_msi_step m.parent (.no_queue e i) p') :
    SimInv { m with parent := p' } s := by
  cases hp with
  | upgrade_to_M_data_not_avilable_rq1 t a i j hj hst hall =>
    have hmema : m.parent.memory a = s.memory a :=
      h.mem_eq a (fun hc => absurd (hst.symm.trans hc.1) (by decide))
    refine ⟨h.fresh_eq, h.ext_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j'
      exact h.conn j'
    · intro b _
      exact h.mem_eq b (fun hc => absurd (hst.symm.trans hc.1) (by decide))
    · intro hpI
      exact absurd (show Bstate.M = Bstate.I from hpI) (by decide)
    · intro _ j' k' hj' hk'
      exact absurd ((hall j').symm.trans hj') (by decide)
    · intro _ j'
      exact Or.inr ⟨hall j', (h.epochI hst j').2⟩
    · intro _ _
      exact hmema
    · intro hpS
      exact absurd (show Bstate.M = Bstate.S from hpS) (by decide)
    · intro hpS
      exact absurd (show Bstate.M = Bstate.S from hpS) (by decide)
  | upgrade_to_M_data_not_avilable_rq2 t a i j hj hst hall =>
    have hmema : m.parent.memory a = s.memory a :=
      h.mem_eq a (fun hc => absurd (hst.symm.trans hc.1) (by decide))
    refine ⟨h.fresh_eq, h.ext_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j'
      exact h.conn j'
    · intro b _
      exact h.mem_eq b (fun hc => absurd (hst.symm.trans hc.1) (by decide))
    · intro hpI
      exact absurd (show Bstate.S = Bstate.I from hpI) (by decide)
    · intro hpM
      exact absurd (show Bstate.S = Bstate.M from hpM) (by decide)
    · intro hpM
      exact absurd (show Bstate.S = Bstate.M from hpM) (by decide)
    · intro hpM
      exact absurd (show Bstate.S = Bstate.M from hpM) (by decide)
    · intro _
      exact hmema
    · intro _ j'
      exact Or.inr ⟨hall j', (h.epochI hst j').2⟩
  | dawngrade_safe_parent_rq1 t a i j hj hst hntag hall =>
    have hpval := h.epochM_val hst hall
    have hcl : ∀ j', clean (m.caches j') := by
      intro j'
      rcases h.epochM_slot hst j' with ⟨hsh, _⟩ | ⟨_, hc⟩
      · exact absurd ((hall j').symm.trans hsh) (by decide)
      · exact hc
    refine ⟨h.fresh_eq, h.ext_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j'
      exact h.conn j'
    · intro b _
      show upd m.parent.memory m.parent.parent.mdata.tag m.parent.parent.value b = s.memory b
      by_cases hb : b = m.parent.parent.mdata.tag
      · subst hb
        rw [upd_self]
        exact hpval
      · rw [upd_other _ _ _ _ hb]
        exact h.mem_eq b (fun hc => hb hc.2.symm)
    · intro _ j'
      exact ⟨hall j', hcl j'⟩
    · intro hpM
      exact absurd (show Bstate.I = Bstate.M from hpM) (by decide)
    · intro hpM
      exact absurd (show Bstate.I = Bstate.M from hpM) (by decide)
    · intro hpM
      exact absurd (show Bstate.I = Bstate.M from hpM) (by decide)
    · intro hpS
      exact absurd (show Bstate.I = Bstate.S from hpS) (by decide)
    · intro hpS
      exact absurd (show Bstate.I = Bstate.S from hpS) (by decide)
  | dawngrade_safe_parent_rq2 t a i j hj hst hntag hall =>
    have hcl : ∀ j', clean (m.caches j') := by
      intro j'
      rcases h.epochS_slot hst j' with ⟨hsh, _⟩ | ⟨_, hc⟩
      · exact absurd ((hall j').symm.trans hsh) (by decide)
      · exact hc
    refine ⟨h.fresh_eq, h.ext_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j'
      exact h.conn j'
    · intro b _
      exact h.mem_eq b (fun hc => absurd (hst.symm.trans hc.1) (by decide))
    · intro _ j'
      exact ⟨hall j', hcl j'⟩
    · intro hpM
      exact absurd (show Bstate.I = Bstate.M from hpM) (by decide)
    · intro hpM
      exact absurd (show Bstate.I = Bstate.M from hpM) (by decide)
    · intro hpM
      exact absurd (show Bstate.I = Bstate.M from hpM) (by decide)
    · intro hpS
      exact absurd (show Bstate.I = Bstate.S from hpS) (by decide)
    · intro hpS
      exact absurd (show Bstate.I = Bstate.S from hpS) (by decide)

/-!
## Parent `upd_queue` steps
-/

/-- The parent consuming a dirty write-back `rsIμ` from cache `i`
(`downgrade_from_M_rq1`) preserves the invariant. -/
theorem simInv_parent_wbM {n : Nat} {m : MSIState n} {s : SeqState n}
    {t : Ident} {a : Addr} {v : Value} {i : Fin n} {j : Nat}
    (h : SimInv m s)
    (hj : (m.parent.queue_cip i)[j]? = some (CPEvent.rsIμ t a v))
    (_htag : m.parent.parent.mdata.tag = a)
    (hst : m.parent.parent.mdata.state = Bstate.M) :
    SimInv { m with
        caches := upd m.caches i
          { m.caches i with
              queue_cp := (m.parent.queue_cip i).eraseIdx j,
              queue_pc := m.parent.queue_pci i },
        parent := { m.parent with
            parent := { m.parent.parent with
              value := v,
              mdata := { m.parent.parent.mdata with
                shared_state := upd m.parent.parent.mdata.shared_state i Bstate.I } },
            queue_cip := upd m.parent.queue_cip i
              ((m.parent.queue_cip i).eraseIdx j) } } s := by
  have hcq := (h.conn i).1
  have hpq := (h.conn i).2
  have hjc : (m.caches i).queue_cp[j]? = some (CPEvent.rsIμ t a v) := by
    rw [hcq]; exact hj
  have hmem : CPEvent.rsIμ t a v ∈ (m.caches i).queue_cp := List.mem_of_getElem? hjc
  obtain ⟨-, -, htok, -, hv⟩ := wbM_facts h i hmem
  have hcntM := countP_eraseIdx isWbM hjc
  have hcntS := countP_eraseIdx isWbS hjc
  simp at hcntM hcntS
  have hsum := htok.1
  have hnM : ¬(m.caches i).cache.mdata.state = Bstate.M := by
    intro hM
    rw [if_pos hM] at hsum
    omega
  rw [if_neg hnM] at hsum
  have hstI : (m.caches i).cache.mdata.state = Bstate.I := bstate_eq_I hnM htok.2.2.2.1
  have hclean : clean
      { m.caches i with
          queue_cp := (m.parent.queue_cip i).eraseIdx j,
          queue_pc := m.parent.queue_pci i } := by
    refine ⟨hstI, ?_, ?_, ?_, ?_⟩
    · show (m.parent.queue_pci i).countP isRsM = 0
      rw [← hpq]
      omega
    · show (m.parent.queue_pci i).countP isRsS = 0
      rw [← hpq]
      exact htok.2.1
    · show ((m.parent.queue_cip i).eraseIdx j).countP isWbM = 0
      rw [← hcq]
      omega
    · show ((m.parent.queue_cip i).eraseIdx j).countP isWbS = 0
      rw [← hcq]
      have := htok.2.2.1
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.fresh_eq i]
    · simp [upd_other _ _ _ _ hjj, h.fresh_eq j']
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.ext_eq i]
    · simp [upd_other _ _ _ _ hjj, h.ext_eq j']
  · intro j'
    by_cases hjj : j' = i
    · exact ⟨by simp [hjj], by simp [hjj]⟩
    · refine ⟨?_, ?_⟩
      · show (upd m.caches i _ j').queue_cp = upd m.parent.queue_cip i _ j'
        rw [upd_other _ _ _ _ hjj, upd_other _ _ _ _ hjj]
        exact (h.conn j').1
      · show (upd m.caches i _ j').queue_pc = m.parent.queue_pci j'
        rw [upd_other _ _ _ _ hjj]
        exact (h.conn j').2
  · intro b hb
    exact h.mem_eq b hb
  · intro hpI
    exact absurd (hst.symm.trans hpI) (by decide)
  · intro _ j' k' hj' hk'
    have hj2 : upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.M := hj'
    have hk2 : upd m.parent.parent.mdata.shared_state i Bstate.I k' = Bstate.M := hk'
    by_cases hji : j' = i
    · rw [hji, upd_self] at hj2
      exact absurd hj2 (by decide)
    · by_cases hki : k' = i
      · rw [hki, upd_self] at hk2
        exact absurd hk2 (by decide)
      · rw [upd_other _ _ _ _ hji] at hj2
        rw [upd_other _ _ _ _ hki] at hk2
        exact h.epochM_uniq hst j' k' hj2 hk2
  · intro _ j'
    by_cases hjj : j' = i
    · refine Or.inr ⟨?_, ?_⟩
      · show upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.I
        rw [hjj, upd_self]
      · show clean (upd m.caches i _ j')
        rw [hjj, upd_self]
        exact hclean
    · rcases h.epochM_slot hst j' with ⟨hsh, htk⟩ | ⟨hsh, hc⟩
      · refine Or.inl ⟨?_, ?_⟩
        · show upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.M
          rw [upd_other _ _ _ _ hjj]
          exact hsh
        · show mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
            (upd m.caches i _ j')
          rw [upd_other _ _ _ _ hjj]
          exact htk
      · refine Or.inr ⟨?_, ?_⟩
        · show upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.I
          rw [upd_other _ _ _ _ hjj]
          exact hsh
        · show clean (upd m.caches i _ j')
          rw [upd_other _ _ _ _ hjj]
          exact hc
  · intro _ _
    exact hv
  · intro hpS
    exact absurd (hst.symm.trans hpS) (by decide)
  · intro hpS
    exact absurd (hst.symm.trans hpS) (by decide)

/-- The parent consuming a clean downgrade `rsIσ` from cache `i`
(`downgrade_from_M_rq2`) preserves the invariant. -/
theorem simInv_parent_wbS {n : Nat} {m : MSIState n} {s : SeqState n}
    {t : Ident} {a : Addr} {i : Fin n} {j : Nat}
    (h : SimInv m s)
    (hj : (m.parent.queue_cip i)[j]? = some (CPEvent.rsIσ t a))
    (_htag : m.parent.parent.mdata.tag = a)
    (hst : m.parent.parent.mdata.state = Bstate.S) :
    SimInv { m with
        caches := upd m.caches i
          { m.caches i with
              queue_cp := (m.parent.queue_cip i).eraseIdx j,
              queue_pc := m.parent.queue_pci i },
        parent := { m.parent with
            parent := { m.parent.parent with
              mdata := { m.parent.parent.mdata with
                shared_state := upd m.parent.parent.mdata.shared_state i Bstate.I } },
            queue_cip := upd m.parent.queue_cip i
              ((m.parent.queue_cip i).eraseIdx j) } } s := by
  have hcq := (h.conn i).1
  have hpq := (h.conn i).2
  have hjc : (m.caches i).queue_cp[j]? = some (CPEvent.rsIσ t a) := by
    rw [hcq]; exact hj
  have hmem : CPEvent.rsIσ t a ∈ (m.caches i).queue_cp := List.mem_of_getElem? hjc
  obtain ⟨-, -, htok, -⟩ := wbS_facts h i hmem
  have hcntM := countP_eraseIdx isWbM hjc
  have hcntS := countP_eraseIdx isWbS hjc
  simp at hcntM hcntS
  have hsum := htok.1
  have hnS : ¬(m.caches i).cache.mdata.state = Bstate.S := by
    intro hS
    rw [if_pos hS] at hsum
    omega
  rw [if_neg hnS] at hsum
  have hstI : (m.caches i).cache.mdata.state = Bstate.I := bstate_eq_I htok.2.2.2.1 hnS
  have hclean : clean
      { m.caches i with
          queue_cp := (m.parent.queue_cip i).eraseIdx j,
          queue_pc := m.parent.queue_pci i } := by
    refine ⟨hstI, ?_, ?_, ?_, ?_⟩
    · show (m.parent.queue_pci i).countP isRsM = 0
      rw [← hpq]
      exact htok.2.1
    · show (m.parent.queue_pci i).countP isRsS = 0
      rw [← hpq]
      omega
    · show ((m.parent.queue_cip i).eraseIdx j).countP isWbM = 0
      rw [← hcq]
      have := htok.2.2.1
      omega
    · show ((m.parent.queue_cip i).eraseIdx j).countP isWbS = 0
      rw [← hcq]
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.fresh_eq i]
    · simp [upd_other _ _ _ _ hjj, h.fresh_eq j']
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.ext_eq i]
    · simp [upd_other _ _ _ _ hjj, h.ext_eq j']
  · intro j'
    by_cases hjj : j' = i
    · exact ⟨by simp [hjj], by simp [hjj]⟩
    · refine ⟨?_, ?_⟩
      · show (upd m.caches i _ j').queue_cp = upd m.parent.queue_cip i _ j'
        rw [upd_other _ _ _ _ hjj, upd_other _ _ _ _ hjj]
        exact (h.conn j').1
      · show (upd m.caches i _ j').queue_pc = m.parent.queue_pci j'
        rw [upd_other _ _ _ _ hjj]
        exact (h.conn j').2
  · intro b hb
    exact h.mem_eq b hb
  · intro hpI
    exact absurd (hst.symm.trans hpI) (by decide)
  · intro hpM
    exact absurd (hst.symm.trans hpM) (by decide)
  · intro hpM
    exact absurd (hst.symm.trans hpM) (by decide)
  · intro hpM _
    exact absurd (hst.symm.trans hpM) (by decide)
  · intro _
    exact h.epochS_val hst
  · intro _ j'
    by_cases hjj : j' = i
    · refine Or.inr ⟨?_, ?_⟩
      · show upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.I
        rw [hjj, upd_self]
      · show clean (upd m.caches i _ j')
        rw [hjj, upd_self]
        exact hclean
    · rcases h.epochS_slot hst j' with ⟨hsh, htk⟩ | ⟨hsh, hc⟩
      · refine Or.inl ⟨?_, ?_⟩
        · show upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.S
          rw [upd_other _ _ _ _ hjj]
          exact hsh
        · show stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
            (upd m.caches i _ j')
          rw [upd_other _ _ _ _ hjj]
          exact htk
      · refine Or.inr ⟨?_, ?_⟩
        · show upd m.parent.parent.mdata.shared_state i Bstate.I j' = Bstate.I
          rw [upd_other _ _ _ _ hjj]
          exact hsh
        · show clean (upd m.caches i _ j')
          rw [upd_other _ _ _ _ hjj]
          exact hc

/-- The parent answering a `rqM` request with an exclusive data grant
(`upgrade_to_M_data_avilable_rq1`) preserves the invariant. -/
theorem simInv_parent_grantM {n : Nat} {m : MSIState n} {s : SeqState n}
    {t : Ident} {a : Addr} {i : Fin n} {j : Nat}
    (h : SimInv m s)
    (hj : (m.parent.queue_cip i)[j]? = some (CPEvent.rqM t a))
    (hst : m.parent.parent.mdata.state = Bstate.M)
    (htag : m.parent.parent.mdata.tag = a)
    (hall : ∀ i', m.parent.parent.mdata.shared_state i' = Bstate.I) :
    SimInv { m with
        caches := upd m.caches i
          { m.caches i with
              queue_cp := (m.parent.queue_cip i).eraseIdx j,
              queue_pc := m.parent.queue_pci i ++
                [PCEvent.rsM t a m.parent.parent.value] },
        parent := { m.parent with
            parent := { m.parent.parent with
              mdata := { m.parent.parent.mdata with
                shared_state := upd m.parent.parent.mdata.shared_state i Bstate.M } },
            queue_cip := upd m.parent.queue_cip i ((m.parent.queue_cip i).eraseIdx j),
            queue_pci := upd m.parent.queue_pci i
              (m.parent.queue_pci i ++ [PCEvent.rsM t a m.parent.parent.value]) } } s := by
  have hcq := (h.conn i).1
  have hpq := (h.conn i).2
  have hjc : (m.caches i).queue_cp[j]? = some (CPEvent.rqM t a) := by
    rw [hcq]; exact hj
  have hclall : ∀ j', clean (m.caches j') := by
    intro j'
    rcases h.epochM_slot hst j' with ⟨hsh, _⟩ | ⟨_, hc⟩
    · exact absurd ((hall j').symm.trans hsh) (by decide)
    · exact hc
  have hval := h.epochM_val hst hall
  have hcntM := countP_eraseIdx isWbM hjc
  have hcntS := countP_eraseIdx isWbS hjc
  simp at hcntM hcntS
  have herasedM : ((m.parent.queue_cip i).eraseIdx j).countP isWbM = 0 := by
    rw [← hcq]
    have := (hclall i).2.2.2.1
    omega
  have herasedS : ((m.parent.queue_cip i).eraseIdx j).countP isWbS = 0 := by
    rw [← hcq]
    have := (hclall i).2.2.2.2
    omega
  have hpcM : (m.parent.queue_pci i).countP isRsM = 0 := by
    rw [← hpq]
    exact (hclall i).2.1
  have hpcS : (m.parent.queue_pci i).countP isRsS = 0 := by
    rw [← hpq]
    exact (hclall i).2.2.1
  have htokM : mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
      { m.caches i with
          queue_cp := (m.parent.queue_cip i).eraseIdx j,
          queue_pc := m.parent.queue_pci i ++
            [PCEvent.rsM t a m.parent.parent.value] } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (m.parent.queue_pci i ++ [PCEvent.rsM t a m.parent.parent.value]).countP isRsM +
        (if (m.caches i).cache.mdata.state = Bstate.M then 1 else 0) +
        ((m.parent.queue_cip i).eraseIdx j).countP isWbM = 1
      rw [if_neg (fun hc => absurd ((hclall i).1.symm.trans hc) (by decide))]
      simp [List.countP_append, hpcM, herasedM]
    · show (m.parent.queue_pci i ++ [PCEvent.rsM t a m.parent.parent.value]).countP isRsS = 0
      simp [List.countP_append, hpcS]
    · show ((m.parent.queue_cip i).eraseIdx j).countP isWbS = 0
      exact herasedS
    · show ¬(m.caches i).cache.mdata.state = Bstate.S
      intro hc
      exact absurd ((hclall i).1.symm.trans hc) (by decide)
    · intro t' a' v' hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact (not_mem_of_countP_zero hpcM hmem rfl).elim
      · simp only [List.mem_singleton, PCEvent.rsM.injEq] at hmem
        exact ⟨hmem.2.1.trans htag.symm, hmem.2.2.trans hval⟩
    · intro hc
      exact absurd ((hclall i).1.symm.trans hc) (by decide)
    · intro t' a' v' hmem
      exact (not_mem_of_countP_zero herasedM hmem rfl).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.fresh_eq i]
    · simp [upd_other _ _ _ _ hjj, h.fresh_eq j']
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.ext_eq i]
    · simp [upd_other _ _ _ _ hjj, h.ext_eq j']
  · intro j'
    by_cases hjj : j' = i
    · exact ⟨by simp [hjj], by simp [hjj]⟩
    · refine ⟨?_, ?_⟩
      · show (upd m.caches i _ j').queue_cp = upd m.parent.queue_cip i _ j'
        rw [upd_other _ _ _ _ hjj, upd_other _ _ _ _ hjj]
        exact (h.conn j').1
      · show (upd m.caches i _ j').queue_pc = upd m.parent.queue_pci i _ j'
        rw [upd_other _ _ _ _ hjj, upd_other _ _ _ _ hjj]
        exact (h.conn j').2
  · intro b hb
    exact h.mem_eq b hb
  · intro hpI
    exact absurd (hst.symm.trans hpI) (by decide)
  · intro _ j' k' hj' hk'
    have hj2 : upd m.parent.parent.mdata.shared_state i Bstate.M j' = Bstate.M := hj'
    have hk2 : upd m.parent.parent.mdata.shared_state i Bstate.M k' = Bstate.M := hk'
    by_cases hji : j' = i
    · by_cases hki : k' = i
      · rw [hji, hki]
      · rw [upd_other _ _ _ _ hki] at hk2
        exact absurd ((hall k').symm.trans hk2) (by decide)
    · rw [upd_other _ _ _ _ hji] at hj2
      exact absurd ((hall j').symm.trans hj2) (by decide)
  · intro _ j'
    by_cases hjj : j' = i
    · refine Or.inl ⟨?_, ?_⟩
      · show upd m.parent.parent.mdata.shared_state i Bstate.M j' = Bstate.M
        rw [hjj, upd_self]
      · show mtoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
          (upd m.caches i _ j')
        rw [hjj, upd_self]
        exact htokM
    · refine Or.inr ⟨?_, ?_⟩
      · show upd m.parent.parent.mdata.shared_state i Bstate.M j' = Bstate.I
        rw [upd_other _ _ _ _ hjj]
        exact hall j'
      · show clean (upd m.caches i _ j')
        rw [upd_other _ _ _ _ hjj]
        exact hclall j'
  · intro _ hall'
    have h2 : upd m.parent.parent.mdata.shared_state i Bstate.M i = Bstate.I := hall' i
    rw [upd_self] at h2
    exact absurd h2 (by decide)
  · intro hpS
    exact absurd (hst.symm.trans hpS) (by decide)
  · intro hpS
    exact absurd (hst.symm.trans hpS) (by decide)

/-- The parent answering a `rqS` request with a shared data grant
(`upgrade_to_M_data_avilable_rq2`) preserves the invariant. -/
theorem simInv_parent_grantS {n : Nat} {m : MSIState n} {s : SeqState n}
    {t : Ident} {a : Addr} {i : Fin n} {j : Nat}
    (h : SimInv m s)
    (hj : (m.parent.queue_cip i)[j]? = some (CPEvent.rqS t a))
    (hst : m.parent.parent.mdata.state = Bstate.S)
    (htag : m.parent.parent.mdata.tag = a)
    (hsh : m.parent.parent.mdata.shared_state i = Bstate.I) :
    SimInv { m with
        caches := upd m.caches i
          { m.caches i with
              queue_cp := (m.parent.queue_cip i).eraseIdx j,
              queue_pc := m.parent.queue_pci i ++
                [PCEvent.rsS t a m.parent.parent.value] },
        parent := { m.parent with
            parent := { m.parent.parent with
              mdata := { m.parent.parent.mdata with
                shared_state := upd m.parent.parent.mdata.shared_state i Bstate.S } },
            queue_cip := upd m.parent.queue_cip i ((m.parent.queue_cip i).eraseIdx j),
            queue_pci := upd m.parent.queue_pci i
              (m.parent.queue_pci i ++ [PCEvent.rsS t a m.parent.parent.value]) } } s := by
  have hcq := (h.conn i).1
  have hpq := (h.conn i).2
  have hjc : (m.caches i).queue_cp[j]? = some (CPEvent.rqS t a) := by
    rw [hcq]; exact hj
  have hcl : clean (m.caches i) := by
    rcases h.epochS_slot hst i with ⟨hsh0, _⟩ | ⟨_, hc⟩
    · exact absurd (hsh.symm.trans hsh0) (by decide)
    · exact hc
  have hval := h.epochS_val hst
  have hcntM := countP_eraseIdx isWbM hjc
  have hcntS := countP_eraseIdx isWbS hjc
  simp at hcntM hcntS
  have herasedM : ((m.parent.queue_cip i).eraseIdx j).countP isWbM = 0 := by
    rw [← hcq]
    have := hcl.2.2.2.1
    omega
  have herasedS : ((m.parent.queue_cip i).eraseIdx j).countP isWbS = 0 := by
    rw [← hcq]
    have := hcl.2.2.2.2
    omega
  have hpcM : (m.parent.queue_pci i).countP isRsM = 0 := by
    rw [← hpq]
    exact hcl.2.1
  have hpcS : (m.parent.queue_pci i).countP isRsS = 0 := by
    rw [← hpq]
    exact hcl.2.2.1
  have htokS : stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
      { m.caches i with
          queue_cp := (m.parent.queue_cip i).eraseIdx j,
          queue_pc := m.parent.queue_pci i ++
            [PCEvent.rsS t a m.parent.parent.value] } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (m.parent.queue_pci i ++ [PCEvent.rsS t a m.parent.parent.value]).countP isRsS +
        (if (m.caches i).cache.mdata.state = Bstate.S then 1 else 0) +
        ((m.parent.queue_cip i).eraseIdx j).countP isWbS = 1
      rw [if_neg (fun hc => absurd (hcl.1.symm.trans hc) (by decide))]
      simp [List.countP_append, hpcS, herasedS]
    · show (m.parent.queue_pci i ++ [PCEvent.rsS t a m.parent.parent.value]).countP isRsM = 0
      simp [List.countP_append, hpcM]
    · show ((m.parent.queue_cip i).eraseIdx j).countP isWbM = 0
      exact herasedM
    · show ¬(m.caches i).cache.mdata.state = Bstate.M
      intro hc
      exact absurd (hcl.1.symm.trans hc) (by decide)
    · intro t' a' v' hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact (not_mem_of_countP_zero hpcS hmem rfl).elim
      · simp only [List.mem_singleton, PCEvent.rsS.injEq] at hmem
        exact ⟨hmem.2.1.trans htag.symm, hmem.2.2.trans hval⟩
    · intro hc
      exact absurd (hcl.1.symm.trans hc) (by decide)
    · intro t' a' hmem
      exact (not_mem_of_countP_zero herasedS hmem rfl).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.fresh_eq i]
    · simp [upd_other _ _ _ _ hjj, h.fresh_eq j']
  · intro j'
    by_cases hjj : j' = i
    · simp [hjj, h.ext_eq i]
    · simp [upd_other _ _ _ _ hjj, h.ext_eq j']
  · intro j'
    by_cases hjj : j' = i
    · exact ⟨by simp [hjj], by simp [hjj]⟩
    · refine ⟨?_, ?_⟩
      · show (upd m.caches i _ j').queue_cp = upd m.parent.queue_cip i _ j'
        rw [upd_other _ _ _ _ hjj, upd_other _ _ _ _ hjj]
        exact (h.conn j').1
      · show (upd m.caches i _ j').queue_pc = upd m.parent.queue_pci i _ j'
        rw [upd_other _ _ _ _ hjj, upd_other _ _ _ _ hjj]
        exact (h.conn j').2
  · intro b hb
    exact h.mem_eq b hb
  · intro hpI
    exact absurd (hst.symm.trans hpI) (by decide)
  · intro hpM
    exact absurd (hst.symm.trans hpM) (by decide)
  · intro hpM
    exact absurd (hst.symm.trans hpM) (by decide)
  · intro hpM _
    exact absurd (hst.symm.trans hpM) (by decide)
  · intro _
    exact hval
  · intro _ j'
    by_cases hjj : j' = i
    · refine Or.inl ⟨?_, ?_⟩
      · show upd m.parent.parent.mdata.shared_state i Bstate.S j' = Bstate.S
        rw [hjj, upd_self]
      · show stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
          (upd m.caches i _ j')
        rw [hjj, upd_self]
        exact htokS
    · rcases h.epochS_slot hst j' with ⟨hsh0, htk⟩ | ⟨hsh0, hc⟩
      · refine Or.inl ⟨?_, ?_⟩
        · show upd m.parent.parent.mdata.shared_state i Bstate.S j' = Bstate.S
          rw [upd_other _ _ _ _ hjj]
          exact hsh0
        · show stoken m.parent.parent.mdata.tag (s.memory m.parent.parent.mdata.tag)
            (upd m.caches i _ j')
          rw [upd_other _ _ _ _ hjj]
          exact htk
      · refine Or.inr ⟨?_, ?_⟩
        · show upd m.parent.parent.mdata.shared_state i Bstate.S j' = Bstate.I
          rw [upd_other _ _ _ _ hjj]
          exact hsh0
        · show clean (upd m.caches i _ j')
          rw [upd_other _ _ _ _ hjj]
          exact hc

theorem sim_parent_upd {n : Nat} {m : MSIState n} {s : SeqState n} {p' : ParentState n}
    {e : ParentEvent n} {i : Fin n}
    (h : SimInv m s) (hp : parent_msi_step m.parent (.upd_queue e i) p') :
    SimInv { m with
        caches := upd m.caches i
          { m.caches i with queue_cp := p'.queue_cip i, queue_pc := p'.queue_pci i },
        parent := p' } s := by
  cases hp with
  | downgrade_from_M_rq1 t a v i j hj htag hst =>
    simp only [upd_self]
    exact simInv_parent_wbM h hj htag hst
  | downgrade_from_M_rq2 t a i j hj htag hst =>
    simp only [upd_self]
    exact simInv_parent_wbS h hj htag hst
  | upgrade_to_M_data_avilable_rq1 t a i j hj hst htag hall =>
    simp only [upd_self]
    exact simInv_parent_grantM h hj hst htag hall
  | upgrade_to_M_data_avilable_rq2 t a i j hj hst htag hsh =>
    simp only [upd_self]
    exact simInv_parent_grantS h hj hst htag hsh
  | upgrade_to_M_invalid_all t a i i' j hj hntag hst hsh =>
    simp only [upd_self]
    exact simInv_parent_push h _ _ rfl rfl
  | upgrade_to_M_invalid_all1 t a i i' j hj hntag hst hall =>
    simp only [upd_self]
    exact simInv_parent_push h _ _ rfl rfl
  | upgrade_to_M_invalid_all2 t a i i' j hj hntag hst hall =>
    simp only [upd_self]
    exact simInv_parent_push h _ _ rfl rfl
  | upgrade_to_M_invalid_all3 t a i i' j hj hntag hst hsh =>
    simp only [upd_self]
    exact simInv_parent_push h _ _ rfl rfl

theorem sim_internal {n : Nat} {m m' : MSIState n} {s : SeqState n} {e : MIInternalEvent n}
    (h : SimInv m s) (hs : msi_step_internal m e m') :
    ∃ s', star_extend seq_step seq_internal_step s [] s' ∧ SimInv m' s' := by
  cases hs with
  | cache cache' i e hc => exact sim_internal_cache h hc
  | parent_upd_queue parent' e i hp => exact ⟨s, .refl s, sim_parent_upd h hp⟩
  | parent_no_queue parent' e i hp => exact ⟨s, .refl s, sim_parent_no h hp⟩

/-!
## Composition of `star_extend` runs
-/

theorem star_extend_append {State Event IntEvent : Type}
    {ext : State → Event → State → Prop} {int : State → IntEvent → State → Prop}
    {s s₁ s₂ : State} {l₁ l₂ : List Event}
    (h1 : star_extend ext int s l₁ s₁) (h2 : star_extend ext int s₁ l₂ s₂) :
    star_extend ext int s (l₂ ++ l₁) s₂ := by
  induction h2 with
  | refl => exact h1
  | step_int _ _ _ ie _ hint ih => exact .step_int _ _ _ _ ie ih hint
  | step_ext _ _ _ e _ hext ih => exact .step_ext _ _ _ _ e ih hext

/-!
## The main theorems
-/

theorem enough_star {n : Nat} (i i' : MSIState n) (s : SeqState n) (l : List (TaggedEvent n)) :
    φ i s →
    star_extend msi_step_external msi_step_internal i l i' →
    ∃ s', star_extend seq_step seq_internal_step s l s' ∧ φ i' s' := by
  intro hφ hstar
  induction hstar with
  | refl => exact ⟨s, .refl s, hφ⟩
  | step_int _ _ _ ie _ hint ih =>
    obtain ⟨s₁, hs₁, hφ₁⟩ := ih
    obtain ⟨s₂, hs₂, hφ₂⟩ := sim_internal hφ₁ hint
    exact ⟨s₂, by simpa using star_extend_append hs₁ hs₂, hφ₂⟩
  | step_ext _ _ _ e _ hext ih =>
    obtain ⟨s₁, hs₁, hφ₁⟩ := ih
    obtain ⟨s₂, hs₂, hφ₂⟩ := sim_external hφ₁ hext
    exact ⟨s₂, .step_ext _ _ _ _ e hs₁ hs₂, hφ₂⟩

theorem initial_phi :
  @φ n default default := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rfl
  · intro i; rfl
  · intro i; exact ⟨rfl, rfl⟩
  · intro a _; rfl
  · intro _ i; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

end FormalMSI.MSIProof
