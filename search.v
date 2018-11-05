From Mtac2 Require Import Mtac2 Ttactics Sorts.
From Coq Require Import List.
Import M.notations.
Import M.
Import ListNotations.

Module Mtac_V1.

  Check In 1 [1].

  Theorem x_is_in : forall A (x : A) (l r : list A), In x ((x::l) ++ r).
  Proof.
    intros. apply in_or_app. apply or_introl. apply in_eq.
  Qed.
  
  Ltac search x s :=
    match s with
    | x :: ?s' => apply in_eq
    | _ :: ?s' => apply in_cons; search x s'
    | ?l ++ ?r => apply in_or_app; (apply or_introl; search x l) || (apply or_intror; search x r)
    | nil => fail 1
    end.

  Ltac search2 x s :=
    apply in_eq.
  
  Theorem x_is_in2 : forall A (x : A) (l r : list A), In x (l ++ (x :: r)).
  Proof.
    intros. search x (l ++ (x :: r)).
  Qed.
  
  Definition msearch A (x : A) : forall (s : list A), M (In x s) :=
    mfix1 f (s : _) : M (In x s) :=
      mmatch s in (list A) as s' return M (In x s') with 
      | [? l r] l ++ r =>
        mtry
          il <- f l;
          ret (in_or_app l r x (or_introl il))
        with [? e] e =>
          ir <- f r;
          ret (in_or_app l r x (or_intror ir))
        end
      | [? s'] (x :: s') => ret (in_eq _ _)
      | [? y s'] (y :: s') =>
        r <- f s';
        ret (in_cons y x s' r)
      | _ => raise NotFound 
      end.

  Theorem x_is_in3 : forall A (y x : A) (s: list A),
      and (In x (x :: s)) (In x (y :: x :: s)).
  Proof.
    intros. split.
    + mrun (msearch A x (x :: s)).
    + mrun (msearch A x (y :: x :: s)).
  Qed.

  Lemma sub_0_r : forall n, n - 0 = n.
  Proof. intro n. case n; [ | intro n']; reflexivity. Qed.

End Mtac_V1.

Module Mtac_V2.

  Import TT.
  Import TT.notations.

  Definition search {A} (x : A) : forall (s : list A), ttac (In x s) :=
    mfix1 f (s : _) : M (In x s *m _) :=
      mmatch s in (list A) as s' return M (In x s' *m _) with 
      | [? s'] (x :: s') => (apply (@in_eq _ _ _)):(M _)
      | [? y s'] (y :: s') =>
        apply (@in_cons _ y x s') <**> (f s')
      | [? l r] l ++ r =>
        mtry
          apply (@in_or_app _ l r x) <**> (apply (@or_introl _ _) <**> f l)
        with [? e] e =>
          apply (@in_or_app _ l r x) <**> (apply (@or_intror _ _) <**> f r)
        end
      | _ => raise NotFound 
      end.

  Definition search' {A} (x : A) (s : list A) : M (In x s) :=
    lower (search x s).

  Theorem x_in_s1 : forall A (x : A) (s: list A), In x (x :: s).
  MProof. intros A x s. search' x (x :: s). Qed.

  Theorem x_in_s2 : forall A (y x : A) (s: list A), In x (y :: x :: s).
  MProof. intros A y x s. search' x (y :: x :: s). Qed.
  
  Theorem x_in_s3 : forall A (y x : A) (l r: list A), In x ((y :: x :: l) ++ r).
  MProof. intros A y x l r. search' x ((y :: x :: l) ++ r). Qed.
  
  (*
  Goal forall A (x : A) (s : list A), (In x s) -> True.
  intros A x s. destruct s. Show Proof.
  *)
End Mtac_V2.