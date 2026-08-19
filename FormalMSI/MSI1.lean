
import FormalMSI.Star
import FormalMSI.CacheMI
import FormalMSI.SI
--import FormalMSI.MIdef
import FormalMSI.MISequential
import Leanses
import Batteries.Data.List.Basic
import FormalMSI.simp

--import Mathlib.Tactic

import Aesop

open List

namespace FormalMSI.MSI

open Leanses
open FormalMSI.SequentionalMI
open FormalMSI.SI


/-!
# Define Events
-/
inductive Bstate where
  | M -- modify
  | I -- invalid
  | S -- shared

deriving instance BEq, Repr for Bstate

instance : Inhabited Bstate where
  default := Bstate.I

inductive CPEvent where
  | rsIμ (ident: Ident) (addr: Addr) (value : Value)
  | rsIσ (ident: Ident) (addr: Addr)
  | rqS (ident: Ident) (addr: Addr)
  | rqM (ident: Ident) (addr: Addr)

deriving instance BEq for CPEvent

def eqConstr : CPEvent -> CPEvent -> Bool
  | .rsIμ  .. => fun | .rsIμ .. => true
                     | _ => false
  | .rsIσ   .. => fun | .rsIσ  .. => true
                      | _ => false
  | .rqS .. => fun | .rqS .. => true
                   | _ => false
  | .rqM .. => fun | .rqM .. => true
                   | _ => false

def List.peek_same_events (l : List CPEvent) (target : CPEvent) : List CPEvent :=
  match l with
  | a :: rst => if (a == target) then (List.peek_same_events rst target) ++ [target]
                else (List.peek_same_events rst target)
  | [] =>[]

inductive PCEvent where
  | rqIμ  (ident: Ident)
  | rqIσ  (ident: Ident)
  | rsM (ident: Ident) (addr: Addr) (val: Value)
  | rsS (ident: Ident) (addr: Addr) (val: Value)

deriving instance BEq for PCEvent

@[aesop simp, simp]
def conversion_cp_mi (a : MI.CPEvent) : (CPEvent) :=
  match a with
  | MI.CPEvent.rsIμ t a v => MSI.CPEvent.rsIμ t a v
  | MI.CPEvent.rqM t a => MSI.CPEvent.rqM t a

@[aesop simp, simp]
def conversion_cp_si (a : SI.CPEvent) : (CPEvent) :=
  match a with
  | SI.CPEvent.rsIσ t a => MSI.CPEvent.rsIσ t a
  | SI.CPEvent.rqS t a => MSI.CPEvent.rqS t a

@[aesop simp, simp]
def conversion_pc_mi (a : MI.PCEvent) : (PCEvent) :=
  match a with
  | MI.PCEvent.rqIμ t => MSI.PCEvent.rqIμ t
  | MI.PCEvent.rsM t a v => MSI.PCEvent.rsM t a v

-- @[simp]
-- def conversion_pc_mi_reverse (a : PCEvent) : (MI.PCEvent) :=
--   match a with
--   | MSI.PCEvent.rqIμ t => MI.PCEvent.rqIμ t
--   | MSI.PCEvent.rsM t a v => MI.PCEvent.rsM t a v


@[aesop simp, simp]
def conversion_pc_si (a : SI.PCEvent) : (PCEvent) :=
  match a with
  | SI.PCEvent.rqIσ t => MSI.PCEvent.rqIσ t
  | SI.PCEvent.rsS t a v => MSI.PCEvent.rsS t a v


/-!
# Metadate and Parent Metadata
-/

structure Metadata where
  state : Bstate
  tag : Tag

mklenses Metadata
deriving instance BEq, Inhabited for Metadata


structure ParentMetadata (n : Nat) where
  state : Bstate
  tag : Tag
  shared_state : Fin n -> Bstate

instance : Inhabited (ParentMetadata n) where
  default := ParentMetadata.mk default default (fun _ => default)

mklenses ParentMetadata


@[aesop simp, simp]
def conversion_MIBstate  (s : Bstate) : Option MI.Bstate :=
  match s with
  | Bstate.M => MI.Bstate.M
  | Bstate.I => MI.Bstate.I
  | Bstate.S => none

@[aesop simp, simp]
def conversion_SIBstate  (s : Bstate) : Option SI.Bstate :=
  match s with
  | Bstate.M => none
  | Bstate.I => SI.Bstate.I
  | Bstate.S => SI.Bstate.S

/-!
# CacheState and ParentState
-/
structure CacheState where
  cache : Cache Metadata
  queue_cp : List CPEvent
  queue_pc : List PCEvent
  fresh_ident : Ident
  extqueue : RsRqEvent

deriving instance BEq, Inhabited for CacheState

mklenses CacheState


structure ParentState (n : Nat) where
  parent : Cache (ParentMetadata n)
  queue_cip : Fin n -> List CPEvent
  queue_pci : Fin n -> List PCEvent
  memory : Addr -> Value
  --memory : Batteries.RBMap Addr Value compare

mklenses ParentState

instance : Inhabited (ParentState n) where
  default := ParentState.mk default (fun _ => default) (fun _ => default)  default



/-!
# MSI State
-/

open CacheState.l in
open ParentState.l in


--define invariant in connections
@[aesop simp, simp]
def connections (c : Fin n -> CacheState) (p: ParentState n) : Prop :=
  ∀ i : Fin n,
    c^.fin_at i∘∘ queue_cp = (view (queue_cip n∘∘fin_at i) p) ∧ (c^.fin_at i∘∘queue_pc) = (view (queue_pci n∘∘fin_at i) p)



structure MSIState (n : Nat) where
  caches : Fin n -> CacheState
  parent : ParentState n

mklenses MSIState



instance : Inhabited (MSIState n) where
  default:= MSIState.mk default default

@[aesop simp, simp]
def msi_init (n : Nat) : (MSIState n) := Inhabited.default

/-!
# Cache step and Cache internal step
-/


open CacheState.l in
open CacheState.l.fresh_ident in
open RsRqEvent.l in
open Cache.l in
open Metadata.l in


inductive cache_msi_step : CacheState → Event → CacheState → Prop where
  | ld_rq : ∀ s1 a,
      cache_msi_step s1 (Event.ld_rq (view CacheState.l.fresh_ident s1) a)
        <{ s1 with fresh_ident := Nat.succ (view fresh_ident s1),
                   extqueue ∘∘ rq := (s1^.extqueue∘∘rq) ++ [Event.ld_rq (view fresh_ident s1) a]
          }>
  | st_rq : ∀ s1 a v,
      cache_msi_step s1 (Event.st_rq (view fresh_ident s1) a v)
      <{ s1 with fresh_ident := Nat.succ (view fresh_ident s1),
                 extqueue ∘∘ rq := view (extqueue ∘∘ rq) s1 ++ [Event.st_rq (view fresh_ident s1) a v]
      }>
  | ld_rs : ∀ s1 v t rst,
      List.dequeue (view (extqueue ∘∘ rs) s1) = some (rst, Event.ld_rs t v) →
      cache_msi_step s1 (Event.ld_rs t v)
      <{ s1 with extqueue ∘∘ rs := rst
      }>



open CacheState.l in
open RsRqEvent.l in
open Cache.l in
open Metadata.l in


inductive cache_msi_step_internal : CacheState → CacheInternalEvent → CacheState → Prop where
  | ld_rq_data_available : ∀ s1 a t rst,
      view (extqueue ∘∘ rq) s1 = Event.ld_rq t a :: rst →
      view (cache ∘∘ meta _ ∘∘ state) s1 = Bstate.M →
      view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1 = a →
      cache_msi_step_internal s1 (CacheInternalEvent.ld_rs t (view (cache ∘∘ value _) s1 ) a)
        <{ s1 with extqueue ∘∘ rs := view (extqueue ∘∘ rs) s1 ++ [Event.ld_rs t (view (cache ∘∘ value _) s1 )],
                   extqueue ∘∘ rq := rst
        }>
  | ld_rq_data_available1 : ∀ s1 a rst,
      view (extqueue ∘∘ rq) s1 = Event.ld_rq t a :: rst →
      view (cache ∘∘ meta _ ∘∘ state) s1 = Bstate.S →
      view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1 = a →
      cache_msi_step_internal s1 (CacheInternalEvent.ld_rs t (view (cache ∘∘ value _) s1 ) a)
        <{ s1 with extqueue ∘∘ rs := view (extqueue ∘∘ rs) s1 ++ [Event.ld_rs t (view (cache ∘∘ value _) s1 )],
                   extqueue ∘∘ rq := rst
        }>
  | st_rq_M_state : ∀ s1 a v rst,
      view (extqueue ∘∘ rq) s1 = Event.st_rq t a v :: rst →
      view (cache ∘∘ meta _ ∘∘ state) s1 = Bstate.M →
      view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1 = a →
      cache_msi_step_internal s1 (CacheInternalEvent.st_rs t a v)
        <{ s1 with cache ∘∘ value _ := v,
                   extqueue ∘∘ rq := rst
        }>
  | rq_data_not_available : ∀ s1 a t rst,
      view (extqueue ∘∘ rq) s1 = Event.ld_rq t a :: rst ∨ (∃ v, view (extqueue ∘∘ rq) s1 = Event.st_rq t a v :: rst) →
      view (cache ∘∘ meta _ ∘∘ state) s1 = Bstate.M →
      ¬(view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1 = a) →
      cache_msi_step_internal s1 (.rq_data_not_available)
        <{ s1 with queue_cp := view (queue_cp) s1 ++ [CPEvent.rsIμ  t (view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1) (view (cache ∘∘ value _) s1) ],
                   cache ∘∘ meta _ ∘∘ state := Bstate.I
        }>
  | rq_data_not_available1 : ∀ s1 a t rst,
      view (extqueue ∘∘ rq) s1 = Event.ld_rq t a :: rst ∨ (∃ v, view (extqueue ∘∘ rq) s1 = Event.st_rq t a v :: rst) →
      view (cache ∘∘ meta _ ∘∘ state) s1 = Bstate.S →
      ¬(view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1 = a) →
      cache_msi_step_internal s1 (.ld_rq_data_not_availableS)
        <{ s1 with queue_cp := view (queue_cp) s1 ++ [CPEvent.rsIσ  t (view (cache ∘∘ meta _ ∘∘ Metadata.l.tag) s1)],
                   cache ∘∘ meta _ ∘∘ state := Bstate.I
        }>
  | upgrade_from_I_rq : ∀ s1 a t  v rst,
      s1^.extqueue ∘∘ rq = Event.st_rq t a v :: rst →
      s1^.cache ∘∘ meta _ ∘∘ state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rq)
      <{ s1 with queue_cp := (s1^.queue_cp) ++ [CPEvent.rqM t a]
      }>
  | upgrade_from_I_rq1 : ∀ s1 a t rst,
      s1^.extqueue ∘∘ rq = Event.ld_rq t a :: rst →
      s1^.cache ∘∘ meta _ ∘∘ state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rqS)
      <{ s1 with queue_cp := (s1^.queue_cp) ++ [CPEvent.rqS t a]
      }>
  | upgrade_from_I_rs : ∀ s1 a t v j,
      (s1^.queue_pc).get? j = some (PCEvent.rsM t a v) →
      s1^.cache ∘∘ meta _ ∘∘ state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rs a v j)
      <{ s1 with cache ∘∘ meta _ ∘∘ state := Bstate.M,
            cache ∘∘ value _ := v,
            cache ∘∘ meta _ ∘∘ Metadata.l.tag := a,
            queue_pc := List.remove? (s1^.queue_pc) j
      }>
  | upgrade_from_I_rsS : ∀ s1 a t v j,
      (s1^.queue_pc).get? j = some (PCEvent.rsS t a v) →
      s1^.cache ∘∘ meta _ ∘∘ state = Bstate.I →
      cache_msi_step_internal s1 (.upgrade_from_I_rsS a v j)
      <{ s1 with cache ∘∘ meta _ ∘∘ state := Bstate.S,
            cache ∘∘ value _ := v,
            cache ∘∘ meta _ ∘∘ Metadata.l.tag := a,
            queue_pc := List.remove? (s1^.queue_pc) j
      }>
  | downgrade_from_M_rs : ∀ s1 j t,
      (s1^.queue_pc).get? j = some (PCEvent.rqIμ t) →
      s1^.cache ∘∘ meta _ ∘∘ state = Bstate.M  →
      cache_msi_step_internal s1 (.downgrade_from_M_rs t j)
        <{ s1 with cache ∘∘ meta _ ∘∘ state := Bstate.I,
                   queue_pc := List.remove? (s1^.queue_pc) j,
                   queue_cp := (s1^.queue_cp) ++ [CPEvent.rsIμ  t (s1^.cache ∘∘ meta _ ∘∘ Metadata.l.tag) (s1^.cache ∘∘ value _)]
        }>
  | downgrade_from_M_rs1 : ∀ s1 j t,
      (s1^.queue_pc).get? j = some (PCEvent.rqIσ t) →
      s1^.cache ∘∘ meta _ ∘∘ state = Bstate.S  →
      cache_msi_step_internal s1 (.downgrade_from_S_rsS t j)
        <{ s1 with cache ∘∘ meta _ ∘∘ state := Bstate.I,
                   queue_pc := List.remove? (s1^.queue_pc) j,
                   queue_cp := (s1^.queue_cp) ++ [CPEvent.rsIσ  t (s1^.cache ∘∘ meta _ ∘∘ Metadata.l.tag)]
        }>

/-!
# Parent step
-/

open ParentState.l in
open RsRqEvent.l in
open Cache.l in
open ParentMetadata.l in


inductive parent_msi_step : ParentState n → ParentInternalEvent n -> ParentState n → Prop where
  | downgrade_from_M_rq1 : ∀ (p1: ParentState n) t a v i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rsIμ t a v)->
      (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a) ->
      (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.M) ->
      parent_msi_step p1 (.upd_queue (.downgrade_from_M_rq1 j t a v) i)
        <{ p1 with parent n ∘∘ value (ParentMetadata n) := v,
                   parent n∘∘meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i := Bstate.I,
                   queue_cip n∘∘fin_at i := List.remove? (p1^.queue_cip n∘∘fin_at i) j
        }>
  | downgrade_from_M_rq2 : ∀ (p1: ParentState n) t a i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rsIσ  t a)->
      (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a) ->
      (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.S) ->
      parent_msi_step p1 (.upd_queue (.downgrade_from_S_rq1S j t a ) i)
        <{ p1 with parent n∘∘meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i := Bstate.I,
                   queue_cip n∘∘fin_at i := List.remove? (p1^.queue_cip n∘∘fin_at i) j
        }>
  | upgrade_to_M_data_avilable_rq1 : ∀ (p1: ParentState n) t a i j,
    (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqM t a)->
    p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.M ->
    p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a ->
    (∀ i, p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ shared_state n∘∘fin_at i = Bstate.I) ->
    parent_msi_step p1 (.upd_queue (.upgrade_to_M_data_avilable_rq1 j t a) i)
      <{ p1 with parent n∘∘meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i :=  Bstate.M,
               queue_cip n∘∘fin_at i := List.remove? (p1^.queue_cip n∘∘fin_at i) j,
               queue_pci n∘∘fin_at i := (p1^.queue_pci n∘∘fin_at i) ++ [PCEvent.rsM t a (view (parent n ∘∘ value (ParentMetadata n)) p1)]
        }>
  | upgrade_to_M_data_avilable_rq2 : ∀ (p1: ParentState n) t i j,
    (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqS t a)->
    p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.S ->
    p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a ->
    parent_msi_step p1 (.upd_queue (.upgrade_to_S_data_avilable_rq1S j t a) i)
      <{ p1 with parent n∘∘meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i :=  Bstate.S,
                 queue_cip n∘∘fin_at i := List.remove? (p1^.queue_cip n∘∘fin_at i) j,
                 queue_pci n∘∘fin_at i := (p1^.queue_pci n∘∘fin_at i) ++ [PCEvent.rsS t a (view (parent n ∘∘ value (ParentMetadata n)) p1)]
        }>

  | upgrade_to_M_invalid_all : ∀ (p1: ParentState n) t a i i' j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqM t a)->
      ¬(p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a) ->
      (p1^.parent n∘∘meta (ParentMetadata n) ∘∘state n = Bstate.M) ->
      p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i' = Bstate.M ->
      parent_msi_step p1 (.upd_queue (.upgrade_to_M_invalid_all j i t a) i')
        <{ p1 with queue_pci n∘∘fin_at i' := (p1^.queue_pci n∘∘ fin_at i') ++ [PCEvent.rqIμ t]
        }>
  | upgrade_to_M_invalid_all1 : ∀ (p1: ParentState n) a i i' j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqM t a)->
      ¬(p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a) ->
      (p1^.parent n∘∘meta (ParentMetadata n) ∘∘state n = Bstate.S) ->
      (∀ i', p1.parent.meta.shared_state i' = Bstate.S) ->
      parent_msi_step p1 (.upd_queue (.invalid_allS t) i')
        <{ p1 with queue_pci n∘∘fin_at i' := (p1^.queue_pci n∘∘ fin_at i') ++ [PCEvent.rqIσ t]
        }>
  | upgrade_to_M_invalid_all2 : ∀ (p1: ParentState n) t a i' j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqS t a)->
      ¬(p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a) ->
      (p1^.parent n∘∘meta  (ParentMetadata n)∘∘state n = Bstate.S) ->
      (∀ i', ¬(i' = i) -> p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i' = Bstate.S) ->
      parent_msi_step p1 (.upd_queue ( .upgrade_to_S_invalid_2_rq1S j i t a) i')
        <{ p1 with queue_pci n∘∘fin_at i' := (p1^.queue_pci n∘∘ fin_at i') ++ [PCEvent.rqIσ t]
        }>
  | upgrade_to_M_invalid_all3 : ∀ (p1: ParentState n) t a i' i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqS t a)->
      ¬(p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n = a) ->
      (p1^.parent n∘∘meta  (ParentMetadata n)∘∘state n = Bstate.M) ->
      p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i' = Bstate.M->
      parent_msi_step p1 (.upd_queue ( .upgrade_to_M_invalid_all j i t a) i')
        <{ p1 with queue_pci n∘∘fin_at i' := (p1^.queue_pci n∘∘ fin_at i') ++ [PCEvent.rqIμ t]
        }>
  | upgrade_to_M_data_not_avilable_rq1 : ∀ (p1: ParentState n) t a i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqM t a) ->
      p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.I ->
      (∀ i', p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i' = Bstate.I) ->
      parent_msi_step p1 (.no_queue (.upgrade_to_M_data_not_avilable_rq1 j t a) i)
        <{ p1 with parent n ∘∘ meta (ParentMetadata n) ∘∘ state n := Bstate.M,
                   parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n := a,
                   parent n ∘∘ value (ParentMetadata n) := p1^.memory n∘∘fin_at a
         }>
  | upgrade_to_M_data_not_avilable_rq2 : ∀ (p1: ParentState n) t a i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqS t a) ->
      p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.I ->
      (∀ i', p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘shared_state n∘∘fin_at i' = Bstate.I) ->
      parent_msi_step p1 (.no_queue (.upgrade_to_S_data_not_avilable_rq1S j t a) i)
        <{ p1 with parent n ∘∘ meta (ParentMetadata n) ∘∘ state n := Bstate.S,
                   parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n := a,
                   parent n ∘∘ value (ParentMetadata n) := p1^.memory n∘∘fin_at a
         }>
  | dawngrade_safe_parent_rq1 : ∀ (p1: ParentState n) t a i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqM t a) ->
      (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.M) ->
      ¬((p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n) = a) ->
      (∀ i', p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ shared_state n∘∘fin_at i' = Bstate.I )->
      parent_msi_step p1 (.no_queue (.dawngrade_safe_parent_rq1 j t a) i)
        <{ p1 with parent n ∘∘ meta (ParentMetadata n) ∘∘ state n := Bstate.I,
                   memory n∘∘fin_at (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n) := p1^.parent n ∘∘ value (ParentMetadata n)
        }>
  | dawngrade_safe_parent_rq2 : ∀ (p1: ParentState n) t a i j,
      (p1^.queue_cip n∘∘fin_at i).get? j = some (CPEvent.rqS t a) ->
      (p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ state n = Bstate.S) ->
      ¬((p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ ParentMetadata.l.tag n) = a) ->
      (∀ i', p1^.parent n ∘∘ meta (ParentMetadata n) ∘∘ shared_state n∘∘fin_at i' = Bstate.I )->
      parent_msi_step p1 (.no_queue (.dawngrade_safe_parent_rq1S j t a) i)
        <{ p1 with parent n ∘∘ meta (ParentMetadata n) ∘∘ state n := Bstate.I
        }>

/-
# MSI step and MSI internal step
-/

-- @[simp]
-- theorem event_cache_intro : ∀ (p : Fin n), Event.cache InternalEvent.intro p = InternalEventMI.intro p := by
--   intro; simp [*, Event.cache]


open MSIState.l in
open ParentState.l in
open CacheState.l in

inductive msi_step_internal : MSIState n -> MIInternalEvent n -> MSIState n -> Prop where
  | cache : ∀ m1 cache' i e,
    cache_msi_step_internal (m1^.caches n∘∘fin_at i) e cache' →
    @msi_step_internal n m1 (.cache e i)
    <{ m1 with caches n ∘∘ fin_at i:= cache',
               MSIState.l.parent n ∘∘ queue_cip n ∘∘ fin_at i := cache'^.queue_cp,
               MSIState.l.parent n ∘∘ queue_pci n ∘∘ fin_at i := cache'^.queue_pc
    }>
  | parent_upd_queue : ∀ m1 parent' e i,
    parent_msi_step (m1^.parent n) (.upd_queue e i) parent'→
    @msi_step_internal n m1 (.parent (.upd_queue e i))
    <{m1 with caches n∘∘fin_at i∘∘queue_cp := parent'^.(queue_cip n)∘∘fin_at i,
              caches n∘∘fin_at i∘∘queue_pc := parent'^.(queue_pci n)∘∘fin_at i,
              MSIState.l.parent n := parent'
    }>
  | parent_no_queue : ∀ m1 parent' e i,
    parent_msi_step (m1^.parent n) (.no_queue e i) parent' →
    @msi_step_internal n m1 (.parent (.no_queue e i))
    <{ m1 with parent n := parent' }>

open MSIState.l in
open ParentState.l in
open CacheState.l in

inductive msi_step_external : MSIState n -> Event -> MSIState n-> Prop where
  | cache : ∀ m1 e cache' i,
    cache_msi_step (m1^.caches n∘∘fin_at i) e cache' →
    msi_step_external m1 (Event.tag n i e)
    <{m1 with caches n ∘∘ fin_at i := cache',
              MSIState.l.parent n ∘∘ queue_cip n ∘∘ fin_at i := cache'^.queue_cp,
              MSIState.l.parent n ∘∘ queue_pci n ∘∘ fin_at i := cache'^.queue_pc
    }>

def imp_behaviour (n : Nat) := behaviour_extend (msi_init n : MSIState n) msi_step_external msi_step_internal


theorem enough_star (i i' : MSIState n) (s : MI_SI_State n) (l : List Event):
  φ i s -> ( ∀ j, match_event i (s.caches j) (s.parent) e mi_si_e) -> star_extend msi_step_external msi_step_internal i l i' -> ∃ s', star_extend mi_si_step_external mi_si_step_internal s l s' ∧ φ i' s' := by
