From Mtac2 Require Import Mtac2 Ttactics Sorts.
From Coq Require Import List.
From Coq Require Import Classical_Prop.
Import M.notations.
Import M.
Import ListNotations.

(* Get a proof for: forall A (x : A) (s : list A), In x s -> M (not (l = [])) *)

Module Mtac_V1.
  
  Lemma false_imp_true : forall (P : Prop), False -> P.
  Proof. intros P H. destruct H. Qed.

  Theorem l_not_empty : forall A (x : A) (s : list A), In x s -> [] <> s.
  Proof. intros A x s. destruct s.
  + simpl. apply false_imp_true.
  + intros H. apply nil_cons.
  Qed.

  Theorem l_not_empty' : forall A (x : A) (s : list A), In x s -> [] <> s.
  Proof.
    intros A x s H. destruct s.
    + simpl in H. destruct H.
    + Abort.

  Ltac lmatch x s :=
    match s with
    | [] => simpl; intros H; destruct H
    | ?a :: ?s' => intros H; exists a; exists s'; reflexivity
    end.

  Theorem asd : forall A (x : A) (s : list A), In x s -> exists y s', s = y :: s'.
  Proof.
    intros A x s H. destruct s.
    + simpl in H; destruct H.
    + exists a. exists s. reflexivity.
  Qed.
  
  Goal forall A (x : A) (s : list A), In x s -> exists y s', s = y :: s'.
  Proof.
    intros A x s H. destruct s. Abort.
  
  Definition mlmatch {A} (x : A) (s : list A) : In x s -> (exists y z, s = y :: z) :=
     match s as s' return In x s' -> (exists y z, s' = y :: z) with
     | a :: c => fun _ =>
       ex_intro (fun (y : A) => exists z, a :: c = y :: z) a 
       (ex_intro (fun (z : list A) => a :: c = a :: z) c eq_refl)
     | [] => fun H : In x [] =>
       match H return (exists y z, [] = y :: z) with
       end
     end.

  Definition dep_match {A} (x : A) (s : list A) : In x s -> M (exists y z, s = y :: z) :=
   fun (H : In x s) =>
     mmatch existT (In x) s H as s' return M (exists y z, projT1 s' = y :: z) with
     | [? a c H] existT _ (a :: c) H =>
       ret (ex_intro (fun (y : A) => exists z, a :: c = y :: z) a 
       (ex_intro (fun (z : list A) => a :: c = a :: z) c eq_refl))
     | [? H] existT _ [] H => 
       match H:(False) return M (exists y z, [] = y :: z) with
       end
     end.

  Goal forall A (x : A) (s : list A), In x s -> M (exists y s', s = y :: s').
  Proof. intros. Abort. (* mrun (dep_match x s H). *)

End Mtac_V1.

Module Mtac_V2.
  Set Printing All.

  Definition test (x : nat) : M (x = x) :=
    mmatch x as x' return M (x' = x') with
    | 0 => ret (eq_refl 0)
    | [? n] S n => ret (eq_refl (S n))
    end.
 
  Definition expl_match (x : nat) : M (x = x) :=
    let p1 := pbase O (fun _ : meq x 0 => ret (eq_refl 0)) UniMatch in
    let p2 := ptele (fun n : nat =>
            (pbase (S n) (fun _ : meq x (S n) => ret (eq_refl (S n))) UniMatch)) in
    let b1 := branch_pattern p1 in
    let b2 := branch_pattern p2 in
    let ps := [m: b1 | b2] in  
    @mmatch' _ (fun x' : nat => eq x' x') DoesNotMatch x ps.
  
  Check expl_match 10.
  Check test 10.

  Goal forall (x : nat), x = x.
  intros. destruct x. mrun (@mkt (eq O O)). 
  mrun (expl_match O). mrun (expl_match (S x)).

  Lemma test' : forall {A} (x : A), M (x = x).
  Proof. intros. 

End Mtac_V2.
