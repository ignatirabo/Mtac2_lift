From Mtac2 Require Import Mtac2 Ttactics Sorts.
From Coq Require Import List.
Import M.notations.
Import M.
Import ListNotations.

Module Mtac_v1.
  
  Fixpoint lookup (P : Prop) (l : list dyn) : M P :=
    match l with
    | D :: l => mmatch D with | [? (p : P)] Dyn p =u> ret p | _ => lookup P l end
    |     [] => raise NotFound
    end.
  
  Mtac Do New Exception TautoFail.

  Definition solve_tauto : forall (l : list dyn) {P : Prop}, M P :=
    mfix2 f (l : list dyn) (P : Prop) : M P :=
      mtry
        lookup P l
      with NotFound =>
        mmatch P in Prop as P' return M P' with
        | True => ret I
        | [? Q1 Q2] Q1 /\ Q2 =>
          q1 <- f l Q1;
          q2 <- f l Q2;
          ret (conj q1 q2)
        | [? Q1 Q2] Q1 \/ Q2 =>
          mtry
            q1 <- f l Q1; ret (or_introl q1)
          with TautoFail =>
            q2 <- f l Q2; ret (or_intror q2)
          end
        | [? (Q1 Q2 : Prop)] Q1 -> Q2 =>
          \nu q1,
            q2 <- f (Dyn q1 :: l) Q2; abs_fun q1 q2
        | [? X (Q : X -> Prop)] (exists x : X, Q x) =>
          x <- evar X;
          q <- f l (Q x);
          b <- is_evar x;
          if b then
            raise TautoFail
          else
            ret (ex_intro Q x q)
        | _ => raise TautoFail
        end
      end.

  Ltac i := intros H.

  Goal True -> True.
  i; exact H.
  
End Mtac_v1.
