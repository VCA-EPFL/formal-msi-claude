import FormalMSI.Star
import FormalMSI.MSI
import FormalMSI.SeqSpec

/-!
# Refinement of the sequential specification by the MSI protocol

States the simulation theorem `enough_star`: every behaviour of the MSI
implementation (`msi_step_external`/`msi_step_internal`) can be matched by
the sequential specification (`seq_step`/`seq_internal_step`), preserving
the simulation relation `φ`.  Here `φ` is defined as the greatest
simulation relation, so `enough_star` is its unfolding lemma.
-/

namespace FormalMSI.MSIProof

open FormalMSI.MSI
open FormalMSI.SequentionalMI

def φ {n : Nat} (i : MSIState n) (s : SeqState n) : Prop := sorry

theorem enough_star {n : Nat} (i i' : MSIState n) (s : SeqState n) (l : List (TaggedEvent n)) :
    φ i s →
    star_extend msi_step_external msi_step_internal i l i' →
    ∃ s', star_extend seq_step seq_internal_step s l s' ∧ φ i' s' := sorry

theorem initial_phi :
  @φ n default default := sorry

end FormalMSI.MSIProof
