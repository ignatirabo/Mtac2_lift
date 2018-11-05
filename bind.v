From Mtac2 Require Import Base MTele Mtac2.
Import Sorts.S.
Import M.notations.
Import M.M.

Let m := @mTele nat (fun x : nat => @mTele nat (fun y : nat => mBase)).
Let B : MTele_Sort SProp m := fun x y => x = y.
Eval cbn in MTele_Sort SProp m.
Let b : MTele_val (MTele_C SProp SProp M B) := fun x y => M.failwith "".
Eval cbn in MTele_val (MTele_C SProp SProp M B).

Let o := @mTele nat (fun x : nat => mBase).
Let C : MTele_Sort SProp o := fun x => x = x. (* C is nat -> Prop : Type *)

Eval cbn in MTele_Ty o.
Eval cbn in MTele_val (MTele_C SProp SProp M C).


Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

Definition bind1 {A : Type} {C : Type} {B : forall (c : C), Type} : M A -> (A -> forall (c : C), M (B c)) -> forall (c : C), M (B c) :=
  fun ma f c => @bind A (B c) ma (fun a => f a c).

Definition bind2 {A C: Type} {D : C -> Type} {B : forall (c : C) (d : D c), Type} : M A -> (A -> forall (c : C) (d : D c), M (B c d)) -> forall (c : C) (d : D c), M (B c d) :=
  fun ma f c => @bind1 A (D c) (B c) ma (fun a d => f a c d).

Fixpoint mbind {m : MTele} {A : Type} : forall {B : MTele_Ty m}, M A -> (A -> MFA B) -> MFA B :=
  match m with
  | mBase => fun B ma f => @bind A B ma f 
  | @mTele X F => fun B ma f x => @mbind (F x) A (B x) ma (fun a => f a x)
  end.

Notation "'[withP' now_ty , now_val '=>' t ]" :=
  (MTele_In (SProp) (fun now_ty now_val => t))
(at level 0, format "[withP now_ty , now_val => t ]").

Fixpoint mbind' {m : MTele} : forall {A B : MTele_Ty m},
                              MFA A ->
                              (MTele_val [withP ty , _ =>
                                let A' := ty SType A in
                                let B' := ty SType B in
                                (A' -> M B')]) ->
                              MFA B :=
  match m with
  | mBase => fun A B ma f => @mbind mBase A B ma f 
  | @mTele X F => fun A B ma f x => @mbind' (F x) (A x) (B x) (ma x) (f x)
  end.
(*
Fixpoint mbind'' {m : MTele} : forall {A B : MTele_Ty m}, MFA A -> (MTele_val A -> MFA B) -> MFA B :=
  match m with
  | mBase => fun A B ma f => @mbind mBase A B ma f
  | @mTele X F => fun A B ma f x => @mbind'' (F x) (A x) (B x) (ma x) (fun a => (f (ltac:(simpl in *; exact _))) x)
  end.

Fixpoint mbind''' {n m : MTele} : forall {A : MTele_Ty n} {B : MTele_Ty m}, MFA A -> (MTele_val A -> MFA B) -> MFA B :=
  match n with
  | mBase => fun A B ma f => @mbind m A B ma f
  | @mTele X F => fun A B ma f => _
  end.
*)

(*
Definition f A (a : A) : M {A' : Type & A'}.
*)

Definition print_ms (A : Type) : M unit :=
  (mfix1 f (A : Type) : M unit :=
    mmatch A in Type as A' return M unit with
    | [? T] (M T):Type => print_term T
    | [? T (V : forall x : T, Type )] (forall t : T, V t) => f T ;; \nu_f for A as t : T, f (V t)
    | _ => ret (tt)
    end) A.

Definition print_ms' {A} (a : A) := print_ms A.

Goal unit.
mrun (print_ms' (@ret)).

Definition bla (A : Type) : M Type :=
  (mfix1 f (A : Type) : M Type :=
    mmatch A in Type as A' return M Type with
    | [? T] (M T):Type => id (ret (T))
    | [? T (V : forall x : T, Type )] (forall t : T, V t) => \nu_f for A as t : T, @bind (Type) (Type) (f T) (fun a : Type => f (V t))
    | _ => ret (A)
    end) A.

Definition bla' {A} (a : A) := bla A.

