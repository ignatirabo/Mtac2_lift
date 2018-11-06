From Mtac2 Require Import Base MTele Mtac2.
Import Sorts.S.
Import M.notations.
Import M.M.

Module V1.

  Definition lift (A : Type) (m : MTele) : M Type :=
    (mfix1 f (A : Type) : M Type :=
      mmatch A in Type as A' return M Type with
      | [? T] (M T):Type => ret (MTele_ConstT T m)
      | [? T1 T2] T1 -> T2 => t1 <- f T1;
                              t2 <- f T2;
                              ret (t1 -> t2)
      | [? T (V : forall x : T, Type)] (forall t : T, V t) => \nu_f for A as t : T,
                                                                v1 <- f (V t);
                                                                abs_prod_type t v1
      | _ => ret (A)
      end) A.

  Definition lift' {A} (m : MTele) (a : A) := lift A m.

  Goal MTele -> Type.
  intros m.
  mrun (lift (M nat) m).
  Show Proof. Abort.

End V1.

Module V2.
  
  Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

  Definition repl {m : MTele} (A : MTele_Ty m) := MTele_val A.
  
  Definition hold {T : Type} (V : T -> Type) {m : MTele} (A : SType) : T -> Type := V .
  (* Set Printing Universes. *)
  Definition lift (A : Type) (m : MTele) : M Type :=
    (mfix1 f (A : Type) : M Type :=
      M.print_term A;;
      mmatch A in Type as A' return M Type with
      | [? m A] @repl m A => ret (MTele_val A)
      | [? A] (M (@repl m A)):Type => ret ((MFA A):Type)
      | [? A] (M A):Type => ret (MTele_ConstT A m)
      | [? T1 T2] T1 -> T2 =>
        M.print "implication";;
        t1 <- f T1;
        t2 <- f T2;
        ret (t1 -> t2)
      | [? (V : forall X : Type, Type)] (forall X : Type, V X) => M.print "forall1";; \nu_f for A as X : MTele_Ty m,
                                                                    v <- f (V (@repl m X));
                                                                    abs_prod_type X v
      | [? (V : forall X : Type, Prop)] (forall X : Type, V X):Type =>
        M.print "forall1";;
        \nu_f for A as X : MTele_Ty m,
          let x := reduce (RedOneStep [rl:RedBeta]) (V (@repl m X)) in
          v <- f (x);
          abs_prod_type X v
      | [? T (V : forall x : T, Type)] (forall t : T, V t) => M.print "forall2";; \nu_f for A as t : T,
                                                                v1 <- f (V t);
                                                                abs_prod_type t v1
      | [? m V A] (V (@repl m A)) => M.failwith "Unused repl"
      | _ => ret (A)
      end) A.

  Definition lift' {A} (a : A) (m : MTele) := lift A m.

  Goal MTele -> Type.
  intros m.
  mrun (lift' (@ret) m).
  Show Proof. Abort.

End V2.

@bind A (B c) ma (fun a => f a c)