Definition tactic := goal -> M (list goal).

Inductive goal :=
  | Metavar : forall {A}, A -> goal
  | AHyp : forall {A}, (A -> goal) -> goal
  | HypRem : forall {A}, A -> goal -> goal.

Definition ttac A := M (A * list goal).