import FormalMSI.Star

/-!
# MSI cache-coherence protocol

A compiling recreation of the `MSI1.lean` sketch, using plain inductive
definitions and structure updates instead of the `Leanses` lens library.
The base types (`Event`, `RsRqEvent`, `Cache`, internal events, …) that the
sketch imported from `FormalMSI.CacheMI` are defined here directly.
-/

namespace FormalMSI.MSI

/-!
# Base types
-/

abbrev Ident := Nat
abbrev Addr := Nat
abbrev Value := Nat
abbrev Tag := Addr

/-- External events exchanged between a core and its cache: load/store
requests and load responses. -/
inductive Event where
  | ld_rq (ident : Ident) (addr : Addr)
  | st_rq (ident : Ident) (addr : Addr) (value : Value)
  | ld_rs (ident : Ident) (value : Value)
deriving BEq, Repr, DecidableEq

/-- An external event tagged with the index of the cache it belongs to
(the sketch wrote this as `Event.tag n i e`). -/
inductive TaggedEvent (n : Nat) where
  | tag (i : Fin n) (e : Event)
deriving BEq, Repr, DecidableEq

/-- External request/response queues of one cache. -/
structure RsRqEvent where
  rq : List Event := []
  rs : List Event := []
deriving BEq, Repr, Inhabited

/-!
# Define Events
-/

inductive Bstate where
  | M -- modified
  | S -- shared
  | I -- invalid
deriving BEq, Repr, DecidableEq

instance : Inhabited Bstate where
  default := Bstate.I

/-- Child-to-parent events. -/
inductive CPEvent where
  | rsIμ (ident : Ident) (addr : Addr) (value : Value)
  | rsIσ (ident : Ident) (addr : Addr)
  | rqS (ident : Ident) (addr : Addr)
  | rqM (ident : Ident) (addr : Addr)
deriving BEq, Repr, DecidableEq

/-- Equality of constructors only, ignoring the arguments. -/
def eqConstr : CPEvent → CPEvent → Bool
  | .rsIμ .. => fun | .rsIμ .. => true
                    | _ => false
  | .rsIσ .. => fun | .rsIσ .. => true
                    | _ => false
  | .rqS .. => fun | .rqS .. => true
                   | _ => false
  | .rqM .. => fun | .rqM .. => true
                   | _ => false

def peek_same_events (l : List CPEvent) (target : CPEvent) : List CPEvent :=
  match l with
  | a :: rst => if a == target then peek_same_events rst target ++ [target]
                else peek_same_events rst target
  | [] => []

/-- Parent-to-child events. -/
inductive PCEvent where
  | rqIμ (ident : Ident)
  | rqIσ (ident : Ident)
  | rsM (ident : Ident) (addr : Addr) (val : Value)
  | rsS (ident : Ident) (addr : Addr) (val : Value)
deriving BEq, Repr, DecidableEq

/-!
# Metadata and Parent Metadata
-/

structure Metadata where
  state : Bstate
  tag : Tag
deriving BEq, Repr, Inhabited

/-- A single cache line: metadata together with the stored value. -/
structure Cache (M : Type) where
  mdata : M
  value : Value
deriving BEq, Repr

instance [Inhabited M] : Inhabited (Cache M) where
  default := Cache.mk default default

structure ParentMetadata (n : Nat) where
  state : Bstate
  tag : Tag
  shared_state : Fin n → Bstate

instance : Inhabited (ParentMetadata n) where
  default := ParentMetadata.mk default default (fun _ => default)

/-!
# CacheState and ParentState
-/

structure CacheState where
  cache : Cache Metadata
  queue_cp : List CPEvent
  queue_pc : List PCEvent
  fresh_ident : Ident
  extqueue : RsRqEvent
deriving BEq, Repr, Inhabited

structure ParentState (n : Nat) where
  parent : Cache (ParentMetadata n)
  queue_cip : Fin n → List CPEvent
  queue_pci : Fin n → List PCEvent
  memory : Addr → Value

instance : Inhabited (ParentState n) where
  default := ParentState.mk default (fun _ => default) (fun _ => default) default

/-!
# MSI State
-/

structure MSIState (n : Nat) where
  caches : Fin n → CacheState
  parent : ParentState n

instance : Inhabited (MSIState n) where
  default := MSIState.mk default default

/-- Pointwise update of a function at a single point. -/
def upd {α β : Type _} [DecidableEq α] (f : α → β) (x : α) (v : β) : α → β :=
  fun y => if y = x then v else f y

/-- Invariant relating the queues stored in the caches with the queues
stored in the parent. -/
def connections (c : Fin n → CacheState) (p : ParentState n) : Prop :=
  ∀ i : Fin n,
    (c i).queue_cp = p.queue_cip i ∧ (c i).queue_pc = p.queue_pci i

def msi_init (n : Nat) : MSIState n := Inhabited.default

/-!
# Internal events
-/

/-- Internal events of a single cache. -/
inductive CacheInternalEvent where
  | ld_rs (ident : Ident) (value : Value) (addr : Addr)
  | st_rs (ident : Ident) (addr : Addr) (value : Value)
  | rq_data_not_available
  | ld_rq_data_not_availableS
  | upgrade_from_I_rq
  | upgrade_from_I_rqS
  | upgrade_from_I_rs (addr : Addr) (value : Value) (j : Nat)
  | upgrade_from_I_rsS (addr : Addr) (value : Value) (j : Nat)
  | downgrade_from_M_rs (ident : Ident) (j : Nat)
  | downgrade_from_S_rsS (ident : Ident) (j : Nat)
deriving BEq, Repr, DecidableEq

/-- Internal events of the parent. -/
inductive ParentEvent (n : Nat) where
  | downgrade_from_M_rq1 (j : Nat) (t : Ident) (a : Addr) (v : Value)
  | downgrade_from_S_rq1S (j : Nat) (t : Ident) (a : Addr)
  | upgrade_to_M_data_avilable_rq1 (j : Nat) (t : Ident) (a : Addr)
  | upgrade_to_S_data_avilable_rq1S (j : Nat) (t : Ident) (a : Addr)
  | upgrade_to_M_invalid_all (j : Nat) (i : Fin n) (t : Ident) (a : Addr)
  | invalid_allS (t : Ident)
  | upgrade_to_S_invalid_2_rq1S (j : Nat) (i : Fin n) (t : Ident) (a : Addr)
  | upgrade_to_M_data_not_avilable_rq1 (j : Nat) (t : Ident) (a : Addr)
  | upgrade_to_S_data_not_avilable_rq1S (j : Nat) (t : Ident) (a : Addr)
  | dawngrade_safe_parent_rq1 (j : Nat) (t : Ident) (a : Addr)
  | dawngrade_safe_parent_rq1S (j : Nat) (t : Ident) (a : Addr)
deriving BEq, Repr, DecidableEq

/-- A parent internal event, recording whether it also updates the queue
copies held by cache `i` (`upd_queue`) or not (`no_queue`). -/
inductive ParentInternalEvent (n : Nat) where
  | upd_queue (e : ParentEvent n) (i : Fin n)
  | no_queue (e : ParentEvent n) (i : Fin n)
deriving BEq, Repr, DecidableEq

/-- Internal events of the whole system. -/
inductive MIInternalEvent (n : Nat) where
  | cache (e : CacheInternalEvent) (i : Fin n)
  | parent (e : ParentInternalEvent n)
deriving BEq, Repr, DecidableEq

/-!
# Cache step and cache internal step
-/

inductive cache_msi_step : CacheState → Event → CacheState → Prop where
  | ld_rq : ∀ (s1 : CacheState) (a : Addr),
      cache_msi_step s1 (.ld_rq s1.fresh_ident a)
        { s1 with
            fresh_ident := s1.fresh_ident.succ,
            extqueue := { s1.extqueue with
              rq := s1.extqueue.rq ++ [Event.ld_rq s1.fresh_ident a] } }
  | st_rq : ∀ (s1 : CacheState) (a : Addr) (v : Value),
      cache_msi_step s1 (.st_rq s1.fresh_ident a v)
        { s1 with
            fresh_ident := s1.fresh_ident.succ,
            extqueue := { s1.extqueue with
              rq := s1.extqueue.rq ++ [Event.st_rq s1.fresh_ident a v] } }
  | ld_rs : ∀ (s1 : CacheState) (v : Value) (t : Ident) (rst : List Event),
      s1.extqueue.rs = Event.ld_rs t v :: rst →
      cache_msi_step s1 (.ld_rs t v)
        { s1 with extqueue := { s1.extqueue with rs := rst } }

inductive cache_msi_step_internal : CacheState → CacheInternalEvent → CacheState → Prop where
  | ld_rq_data_available : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (rst : List Event),
      s1.extqueue.rq = Event.ld_rq t a :: rst →
      s1.cache.mdata.state = Bstate.M →
      s1.cache.mdata.tag = a →
      cache_msi_step_internal s1 (.ld_rs t s1.cache.value a)
        { s1 with
            extqueue := { s1.extqueue with
              rs := s1.extqueue.rs ++ [Event.ld_rs t s1.cache.value],
              rq := rst } }
  | ld_rq_data_available1 : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (rst : List Event),
      s1.extqueue.rq = Event.ld_rq t a :: rst →
      s1.cache.mdata.state = Bstate.S →
      s1.cache.mdata.tag = a →
      cache_msi_step_internal s1 (.ld_rs t s1.cache.value a)
        { s1 with
            extqueue := { s1.extqueue with
              rs := s1.extqueue.rs ++ [Event.ld_rs t s1.cache.value],
              rq := rst } }
  | st_rq_M_state : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (v : Value) (rst : List Event),
      s1.extqueue.rq = Event.st_rq t a v :: rst →
      s1.cache.mdata.state = Bstate.M →
      s1.cache.mdata.tag = a →
      cache_msi_step_internal s1 (.st_rs t a v)
        { s1 with
            cache := { s1.cache with value := v },
            extqueue := { s1.extqueue with rq := rst } }
  | rq_data_not_available : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (rst : List Event),
      (s1.extqueue.rq = Event.ld_rq t a :: rst ∨
        (∃ v, s1.extqueue.rq = Event.st_rq t a v :: rst)) →
      s1.cache.mdata.state = Bstate.M →
      ¬(s1.cache.mdata.tag = a) →
      cache_msi_step_internal s1 .rq_data_not_available
        { s1 with
            queue_cp := s1.queue_cp ++ [CPEvent.rsIμ t s1.cache.mdata.tag s1.cache.value],
            cache := { s1.cache with mdata := { s1.cache.mdata with state := Bstate.I } } }
  | rq_data_not_available1 : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (rst : List Event),
      (s1.extqueue.rq = Event.ld_rq t a :: rst ∨
        (∃ v, s1.extqueue.rq = Event.st_rq t a v :: rst)) →
      s1.cache.mdata.state = Bstate.S →
      ¬(s1.cache.mdata.tag = a) →
      cache_msi_step_internal s1 .ld_rq_data_not_availableS
        { s1 with
            queue_cp := s1.queue_cp ++ [CPEvent.rsIσ t s1.cache.mdata.tag],
            cache := { s1.cache with mdata := { s1.cache.mdata with state := Bstate.I } } }
  | upgrade_from_I_rq : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (v : Value) (rst : List Event),
      s1.extqueue.rq = Event.st_rq t a v :: rst →
      s1.cache.mdata.state = Bstate.I →
      cache_msi_step_internal s1 .upgrade_from_I_rq
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqM t a] }
  | upgrade_from_I_rq1 : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (rst : List Event),
      s1.extqueue.rq = Event.ld_rq t a :: rst →
      s1.cache.mdata.state = Bstate.I →
      cache_msi_step_internal s1 .upgrade_from_I_rqS
        { s1 with queue_cp := s1.queue_cp ++ [CPEvent.rqS t a] }
  | upgrade_from_I_rs : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (v : Value) (j : Nat),
      s1.queue_pc[j]? = some (PCEvent.rsM t a v) →
      s1.cache.mdata.state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rs a v j)
        { s1 with
            cache := { mdata := { state := Bstate.M, tag := a }, value := v },
            queue_pc := s1.queue_pc.eraseIdx j }
  | upgrade_from_I_rsS : ∀ (s1 : CacheState) (a : Addr) (t : Ident) (v : Value) (j : Nat),
      s1.queue_pc[j]? = some (PCEvent.rsS t a v) →
      s1.cache.mdata.state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rsS a v j)
        { s1 with
            cache := { mdata := { state := Bstate.S, tag := a }, value := v },
            queue_pc := s1.queue_pc.eraseIdx j }
  | downgrade_from_M_rs : ∀ (s1 : CacheState) (j : Nat) (t : Ident),
      s1.queue_pc[j]? = some (PCEvent.rqIμ t) →
      s1.cache.mdata.state = Bstate.M →
      cache_msi_step_internal s1 (.downgrade_from_M_rs t j)
        { s1 with
            cache := { s1.cache with mdata := { s1.cache.mdata with state := Bstate.I } },
            queue_pc := s1.queue_pc.eraseIdx j,
            queue_cp := s1.queue_cp ++ [CPEvent.rsIμ t s1.cache.mdata.tag s1.cache.value] }
  | downgrade_from_M_rs1 : ∀ (s1 : CacheState) (j : Nat) (t : Ident),
      s1.queue_pc[j]? = some (PCEvent.rqIσ t) →
      s1.cache.mdata.state = Bstate.S →
      cache_msi_step_internal s1 (.downgrade_from_S_rsS t j)
        { s1 with
            cache := { s1.cache with mdata := { s1.cache.mdata with state := Bstate.I } },
            queue_pc := s1.queue_pc.eraseIdx j,
            queue_cp := s1.queue_cp ++ [CPEvent.rsIσ t s1.cache.mdata.tag] }

/-!
# Parent step
-/

inductive parent_msi_step {n : Nat} : ParentState n → ParentInternalEvent n → ParentState n → Prop where
  | downgrade_from_M_rq1 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (v : Value) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rsIμ t a v) →
      p1.parent.mdata.tag = a →
      p1.parent.mdata.state = Bstate.M →
      parent_msi_step p1 (.upd_queue (.downgrade_from_M_rq1 j t a v) i)
        { p1 with
            parent := { p1.parent with
              value := v,
              mdata := { p1.parent.mdata with
                shared_state := upd p1.parent.mdata.shared_state i Bstate.I } },
            queue_cip := upd p1.queue_cip i ((p1.queue_cip i).eraseIdx j) }
  | downgrade_from_M_rq2 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rsIσ t a) →
      p1.parent.mdata.tag = a →
      p1.parent.mdata.state = Bstate.S →
      parent_msi_step p1 (.upd_queue (.downgrade_from_S_rq1S j t a) i)
        { p1 with
            parent := { p1.parent with
              mdata := { p1.parent.mdata with
                shared_state := upd p1.parent.mdata.shared_state i Bstate.I } },
            queue_cip := upd p1.queue_cip i ((p1.queue_cip i).eraseIdx j) }
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM t a) →
      p1.parent.mdata.state = Bstate.M →
      p1.parent.mdata.tag = a →
      (∀ i', p1.parent.mdata.shared_state i' = Bstate.I) →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_data_avilable_rq1 j t a) i)
        { p1 with
            parent := { p1.parent with
              mdata := { p1.parent.mdata with
                shared_state := upd p1.parent.mdata.shared_state i Bstate.M } },
            queue_cip := upd p1.queue_cip i ((p1.queue_cip i).eraseIdx j),
            queue_pci := upd p1.queue_pci i
              (p1.queue_pci i ++ [PCEvent.rsM t a p1.parent.value]) }
  | upgrade_to_M_data_avilable_rq2 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS t a) →
      p1.parent.mdata.state = Bstate.S →
      p1.parent.mdata.tag = a →
      p1.parent.mdata.shared_state i = Bstate.I ->
      parent_msi_step p1 (.upd_queue (.upgrade_to_S_data_avilable_rq1S j t a) i)
        { p1 with
            parent := { p1.parent with
              mdata := { p1.parent.mdata with
                shared_state := upd p1.parent.mdata.shared_state i Bstate.S } },
            queue_cip := upd p1.queue_cip i ((p1.queue_cip i).eraseIdx j),
            queue_pci := upd p1.queue_pci i
              (p1.queue_pci i ++ [PCEvent.rsS t a p1.parent.value]) }
  | upgrade_to_M_invalid_all : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i i' : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM t a) →
      ¬(p1.parent.mdata.tag = a) →
      p1.parent.mdata.state = Bstate.M →
      p1.parent.mdata.shared_state i' = Bstate.M →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all j i t a) i')
        { p1 with
            queue_pci := upd p1.queue_pci i' (p1.queue_pci i' ++ [PCEvent.rqIμ t]) }
  | upgrade_to_M_invalid_all1 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i i' : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM t a) →
      ¬(p1.parent.mdata.tag = a) →
      p1.parent.mdata.state = Bstate.S →
      (∀ i'', p1.parent.mdata.shared_state i'' = Bstate.S) →
      parent_msi_step p1 (.upd_queue (.invalid_allS t) i')
        { p1 with
            queue_pci := upd p1.queue_pci i' (p1.queue_pci i' ++ [PCEvent.rqIσ t]) }
  | upgrade_to_M_invalid_all2 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i i' : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS t a) →
      ¬(p1.parent.mdata.tag = a) →
      p1.parent.mdata.state = Bstate.S →
      (∀ i'', ¬(i'' = i) → p1.parent.mdata.shared_state i'' = Bstate.S) →
      parent_msi_step p1 (.upd_queue (.upgrade_to_S_invalid_2_rq1S j i t a) i')
        { p1 with
            queue_pci := upd p1.queue_pci i' (p1.queue_pci i' ++ [PCEvent.rqIσ t]) }
  | upgrade_to_M_invalid_all3 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i i' : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS t a) →
      ¬(p1.parent.mdata.tag = a) →
      p1.parent.mdata.state = Bstate.M →
      p1.parent.mdata.shared_state i' = Bstate.M →
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all j i t a) i')
        { p1 with
            queue_pci := upd p1.queue_pci i' (p1.queue_pci i' ++ [PCEvent.rqIμ t]) }
  | upgrade_to_M_data_not_avilable_rq1 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM t a) →
      p1.parent.mdata.state = Bstate.I →
      (∀ i', p1.parent.mdata.shared_state i' = Bstate.I) →
      parent_msi_step p1 (.no_queue (.upgrade_to_M_data_not_avilable_rq1 j t a) i)
        { p1 with
            parent := { p1.parent with
              value := p1.memory a,
              mdata := { p1.parent.mdata with state := Bstate.M, tag := a } } }
  | upgrade_to_M_data_not_avilable_rq2 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS t a) →
      p1.parent.mdata.state = Bstate.I →
      (∀ i', p1.parent.mdata.shared_state i' = Bstate.I) →
      parent_msi_step p1 (.no_queue (.upgrade_to_S_data_not_avilable_rq1S j t a) i)
        { p1 with
            parent := { p1.parent with
              value := p1.memory a,
              mdata := { p1.parent.mdata with state := Bstate.S, tag := a } } }
  | dawngrade_safe_parent_rq1 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqM t a) →
      p1.parent.mdata.state = Bstate.M →
      ¬(p1.parent.mdata.tag = a) →
      (∀ i', p1.parent.mdata.shared_state i' = Bstate.I) →
      parent_msi_step p1 (.no_queue (.dawngrade_safe_parent_rq1 j t a) i)
        { p1 with
            parent := { p1.parent with
              mdata := { p1.parent.mdata with state := Bstate.I } },
            memory := upd p1.memory p1.parent.mdata.tag p1.parent.value }
  | dawngrade_safe_parent_rq2 : ∀ (p1 : ParentState n) (t : Ident) (a : Addr) (i : Fin n) (j : Nat),
      (p1.queue_cip i)[j]? = some (CPEvent.rqS t a) →
      p1.parent.mdata.state = Bstate.S →
      ¬(p1.parent.mdata.tag = a) →
      (∀ i', p1.parent.mdata.shared_state i' = Bstate.I) →
      parent_msi_step p1 (.no_queue (.dawngrade_safe_parent_rq1S j t a) i)
        { p1 with
            parent := { p1.parent with
              mdata := { p1.parent.mdata with state := Bstate.I } } }

/-!
# MSI step and MSI internal step
-/

inductive msi_step_internal {n : Nat} : MSIState n → MIInternalEvent n → MSIState n → Prop where
  | cache : ∀ (m1 : MSIState n) (cache' : CacheState) (i : Fin n) (e : CacheInternalEvent),
      cache_msi_step_internal (m1.caches i) e cache' →
      msi_step_internal m1 (.cache e i)
        { m1 with
            caches := upd m1.caches i cache',
            parent := { m1.parent with
              queue_cip := upd m1.parent.queue_cip i cache'.queue_cp,
              queue_pci := upd m1.parent.queue_pci i cache'.queue_pc } }
  | parent_upd_queue : ∀ (m1 : MSIState n) (parent' : ParentState n) (e : ParentEvent n) (i : Fin n),
      parent_msi_step m1.parent (.upd_queue e i) parent' →
      msi_step_internal m1 (.parent (.upd_queue e i))
        { m1 with
            caches := upd m1.caches i
              { m1.caches i with
                  queue_cp := parent'.queue_cip i,
                  queue_pc := parent'.queue_pci i },
            parent := parent' }
  | parent_no_queue : ∀ (m1 : MSIState n) (parent' : ParentState n) (e : ParentEvent n) (i : Fin n),
      parent_msi_step m1.parent (.no_queue e i) parent' →
      msi_step_internal m1 (.parent (.no_queue e i))
        { m1 with parent := parent' }

inductive msi_step_external {n : Nat} : MSIState n → TaggedEvent n → MSIState n → Prop where
  | cache : ∀ (m1 : MSIState n) (e : Event) (cache' : CacheState) (i : Fin n),
      cache_msi_step (m1.caches i) e cache' →
      msi_step_external m1 (.tag i e)
        { m1 with
            caches := upd m1.caches i cache',
            parent := { m1.parent with
              queue_cip := upd m1.parent.queue_cip i cache'.queue_cp,
              queue_pci := upd m1.parent.queue_pci i cache'.queue_pc } }

def imp_behaviour (n : Nat) :=
  behaviour_extend (msi_init n : MSIState n) msi_step_external msi_step_internal

end FormalMSI.MSI
