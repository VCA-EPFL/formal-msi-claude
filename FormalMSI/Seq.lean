--import Batteries.Data.RBMap
import FormalMSI.CacheMI
import FormalMSI.Star
import Leanses.AbstractLens
import Leanses

open Leanses

namespace FormalMSI.SequentionalMI

structure SeqState (n : Nat) where
  memory : Addr -> Value
  fresh_ident : Fin n -> Ident
  extqueue : Fin n -> RsRqEvent

mklenses SeqState

instance : Inhabited (SeqState n) where
  default := SeqState.mk default default (fun _ => default)

open SeqState.l in
open RsRqEvent.l in

/-- Quite a basic implementation of a sequential memory behaviour, where only
one request can be in flight at one time.  However, the hope would be that by
still allowing for event queues, that it could be extended to view out-of-order
events. -/
inductive seq_step : SeqState n -> Event -> SeqState n -> Prop where
  | ld_rq : ∀ s1  a i,
      seq_step s1 (Event.tag n i (Event.ld_rq (s1^.fresh_ident n∘∘fin_at i) a))
      <{ s1 with fresh_ident n∘∘fin_at i := Nat.succ (s1^.fresh_ident n∘∘fin_at i),
                 extqueue n∘∘fin_at i∘∘rq := ((s1^.extqueue n∘∘fin_at i∘∘rq) ++ [Event.ld_rq (s1^.fresh_ident n∘∘fin_at i) a]) }>
  | st_rq : ∀ s1 a v i,
      seq_step s1 (Event.tag n i (Event.st_rq (s1^.fresh_ident n∘∘fin_at i) a v))
      <{ s1 with fresh_ident n∘∘fin_at i := Nat.succ (s1^.fresh_ident n∘∘fin_at i),
                 extqueue n∘∘fin_at i∘∘rq := ((s1^.extqueue n∘∘fin_at i∘∘rq) ++ [Event.st_rq (s1^.fresh_ident n∘∘fin_at i) a v]) }>
  | ld_rs : ∀ s1 v t rst i,
      s1^.extqueue n∘∘fin_at i∘∘rs = Event.ld_rs t v :: rst →
      seq_step s1 (Event.tag n i (Event.ld_rs t v)) <{ s1 with extqueue n∘∘fin_at i∘∘rs := rst }>

open SeqState.l in
open RsRqEvent.l in
inductive seq_internal_step : SeqState n -> MIInternalEvent n -> SeqState n -> Prop where
  | read : ∀ (s1: SeqState n) t a v i rst,
      s1^.extqueue n∘∘fin_at i∘∘rq = Event.ld_rq t a :: rst →
      s1^.memory n∘∘fin_at a = v ->
      seq_internal_step s1 (MIInternalEvent.cache (CacheInternalEvent.ld_rs t v a) i)
        <{ s1 with extqueue n∘∘fin_at i∘∘rs := ((s1^.extqueue n∘∘fin_at i∘∘rs) ++ [Event.ld_rs t v]),
                   extqueue n∘∘fin_at i∘∘rq := rst }>
  | write :  ∀ (s1: SeqState n) t a v i rst,
      s1^.extqueue n∘∘fin_at i∘∘rq = Event.st_rq t a v :: rst →
      seq_internal_step s1 (MIInternalEvent.cache (CacheInternalEvent.st_rs t a v) i) <{ s1 with extqueue n∘∘fin_at i∘∘rq := rst, memory n∘∘fin_at a := v }>

@[simp]
def seq_init (n : Nat) : SeqState n := Inhabited.default

def spec_behaviour (n : Nat) := behaviour_extend (seq_init n : SeqState n) seq_step seq_internal_step

end FormalMSI.SequentionalMI
