import FormalMSI.MSI
import FormalMSI.Star

/-!
# Sequential memory specification

A compiling recreation of the `Seq.lean` sketch, using plain inductive
definitions and structure updates instead of the `Leanses` lens library.
The base types (`Event`, `TaggedEvent`, `RsRqEvent`, `MIInternalEvent`, …)
that the sketch imported from `FormalMSI.CacheMI` live in `FormalMSI.MSI`.
-/

namespace FormalMSI.SequentionalMI

open FormalMSI.MSI

structure SeqState (n : Nat) where
  memory : Addr → Value
  fresh_ident : Fin n → Ident
  extqueue : Fin n → RsRqEvent

instance : Inhabited (SeqState n) where
  default := SeqState.mk default default (fun _ => default)

/-- Quite a basic implementation of a sequential memory behaviour, where only
one request can be in flight at one time.  However, the hope would be that by
still allowing for event queues, that it could be extended to view out-of-order
events. -/
inductive seq_step {n : Nat} : SeqState n → TaggedEvent n → SeqState n → Prop where
  | ld_rq : ∀ (s1 : SeqState n) (a : Addr) (i : Fin n),
      seq_step s1 (.tag i (.ld_rq (s1.fresh_ident i) a))
        { s1 with
            fresh_ident := upd s1.fresh_ident i (s1.fresh_ident i).succ,
            extqueue := upd s1.extqueue i
              { s1.extqueue i with
                  rq := (s1.extqueue i).rq ++ [Event.ld_rq (s1.fresh_ident i) a] } }
  | st_rq : ∀ (s1 : SeqState n) (a : Addr) (v : Value) (i : Fin n),
      seq_step s1 (.tag i (.st_rq (s1.fresh_ident i) a v))
        { s1 with
            fresh_ident := upd s1.fresh_ident i (s1.fresh_ident i).succ,
            extqueue := upd s1.extqueue i
              { s1.extqueue i with
                  rq := (s1.extqueue i).rq ++ [Event.st_rq (s1.fresh_ident i) a v] } }
  | ld_rs : ∀ (s1 : SeqState n) (v : Value) (t : Ident) (rst : List Event) (i : Fin n),
      (s1.extqueue i).rs = Event.ld_rs t v :: rst →
      seq_step s1 (.tag i (.ld_rs t v))
        { s1 with extqueue := upd s1.extqueue i { s1.extqueue i with rs := rst } }

inductive seq_internal_step {n : Nat} : SeqState n → MIInternalEvent n → SeqState n → Prop where
  | read : ∀ (s1 : SeqState n) (t : Ident) (a : Addr) (v : Value) (i : Fin n) (rst : List Event),
      (s1.extqueue i).rq = Event.ld_rq t a :: rst →
      s1.memory a = v →
      seq_internal_step s1 (.cache (.ld_rs t v a) i)
        { s1 with
            extqueue := upd s1.extqueue i
              { s1.extqueue i with
                  rs := (s1.extqueue i).rs ++ [Event.ld_rs t v],
                  rq := rst } }
  | write : ∀ (s1 : SeqState n) (t : Ident) (a : Addr) (v : Value) (i : Fin n) (rst : List Event),
      (s1.extqueue i).rq = Event.st_rq t a v :: rst →
      seq_internal_step s1 (.cache (.st_rs t a v) i)
        { s1 with
            extqueue := upd s1.extqueue i { s1.extqueue i with rq := rst },
            memory := upd s1.memory a v }

@[simp]
def seq_init (n : Nat) : SeqState n := Inhabited.default

def spec_behaviour (n : Nat) :=
  behaviour_extend (seq_init n : SeqState n) seq_step seq_internal_step

end FormalMSI.SequentionalMI
