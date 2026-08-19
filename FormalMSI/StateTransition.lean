namespace state

section

variable {State Event : Type}

section

variable (step : State -> List Event -> State -> Prop)
variable (init : State)

inductive star : State -> List Event -> State -> Prop where
  | refl : forall s1, star s1 [] s1
  | step : forall s1, step s1 e1 s2 -> star s2 e2 s3 -> star s1 (e1 ++ e2) s3

theorem star.plus_one s e s' : step s e s' -> star step s e s' := by
  intros Hstep
  have He : e = e ++ [] := by simp
  rw [He]
  apply star.step <;> first | assumption | apply star.refl

def behaviour (l : List Event): Prop :=
  exists s', star step init l s'

end

class StateTransition where
  init : State
  step : State -> List Event -> State -> Prop

section

variable [trans: @StateTransition State Event]

def st_star : State -> List Event -> State -> Prop :=
  star StateTransition.step

def st_behaviour (l : List Event): Prop :=
  @behaviour State Event StateTransition.step (StateTransition.init Event) l

end

end

section

variable {ImpState SpecState Event : Type}

variable [imp : @StateTransition ImpState Event]
variable [spec : @StateTransition SpecState Event]

def indistinguishable (i: ImpState) (s: SpecState): Prop :=
  forall e i',
    imp.step i e i' → exists s', st_star s e s'

infix:60 " ≺ " => indistinguishable
end

end state
