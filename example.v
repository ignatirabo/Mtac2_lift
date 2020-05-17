From Mtac2 Require Import Mtac2 MTele  meta.MTeleMatch meta.MFix.


Set Universe Polymorphism.

Import M.
Import M.notations.

Definition max (S: Set) : M (S -> S -> S) :=
  mmatch S in Set as S' return M (S' -> S' -> S') with
  | nat => M.ret Nat.max
  end.

(* Set Use Unicoq. *)
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Lemma cons_not_nil {S x l}: @cons S x l <> nil.
discriminate.
Qed.

(* Problem: fixed to nat *)
(*
Definition list_max_nat :=
  mfix f (l: list nat) : l <> nil -> M nat :=
    mtmmatch l as l' return l' <> nil -> M nat with
    | [? e] [e] =m> fun nonE => M.ret e
    | [? e1 e2 l'] (e1 :: e2 :: l') =m> fun nonE =>
      m <- Nat.max e1 e2;
      f (m :: l') cons_not_nil
    end.
*)

(* we can't write this: we need the lifted bind *)
Fail Definition list_max (S: Set)  :=
  max <- max S; (* error, the types clearly do not allow this *)
  (* the mfix has tipe forall ... *)
  (* with l_bind it should be possible? *)
  mfix f (l: list S) : l <> nil -> M S :=
    mtmmatch l as l' return l' <> nil -> M S with
    | [? e] [e] =m> fun nonE=>M.ret e
    | [? e1 e2 l'] (e1 :: e2 :: l') =m> fun nonE =>
      m <- max e1 e2;
      f (m :: l') cons_not_nil
    end.

Require Import curry.
Eval cbn in ltac:(mrun (let T := M.type_of (@M.bind) in to_tree T)).
Require Import Mtac2.lib.Specif.
Import ProdNotations.

Definition lift {A:Type} (c: A) (m : MTele) : M m:{T : TyTree & to_ty T} :=
  tA <- to_tree A;
  oH <- unify (to_ty tA) A UniCoq;
  match oH with
  | mSome H =>
     let c0 :=  internal_meq_rew_r Type (to_ty tA) A (fun A0 : Type => A0) c H in
     l <- lift' c0 m;
     M.dbg_term "l: " l;;
     M.ret l

  | mNone => raise CantCoerce
  end.

(* Definition unfold_type_of {A} (c: A) := *)
(*   let T := dreduce (@type_of) (type_of c) in *)
(*   M.dbg_term "T: " T;; *)
(*   M.ret T. *)
(* Notation "'ty_of' x" := (ltac:(mrun (unfold_type_of x))) (at level 0). *)


(* Notation "c † m" := (ltac:(mrun ( *)
(*   (* tA <- to_tree C; *) *)
(*   (* c' <- coerce c; *) *)
(*   C' <- unfold_type_of c; *)
(*   M.dbg_term "C'" C';; *)
(*   let tA := (ltac: (mrun (to_tree C'))) in *)
(*   @lift' tA c m *)
(* ))) (at level 0). *)

Notation "c † m" := (ltac:(mrun (
  lift c m
))) (at level 0).

Notation "[t: a .. b ]" := (mTele (fun a => .. (mTele (fun b => mBase)) ..)) 
  (a binder, b binder, at level 0).

Definition test_tele_list {S} (l: list S) : MTele := [t: (_ : l <> nil)].

Set Printing Universes.

Set Printing All.
Definition bla := (@mexistT TyTree (fun T' : TyTree => to_ty T')
   (tyTree_FAVal Type
      (fun x : Type =>
       tyTree_FAVal Type
         (fun x0 : Type =>
          tyTree_imp (tyTree_M x)
            (tyTree_imp (tyTree_imp (tyTree_base x) (tyTree_M x0))
               (@tyTree_MFA (@mTele nat (fun _ : nat => mBase))
                  (@MTele_Cs S.Type_sort
                     (@mTele nat (fun _ : nat => mBase)) x0))))))
   (fun (x x0 : Type) (x1 : to_ty (tyTree_M x))
      (x2 : to_ty (tyTree_imp (tyTree_base x) (tyTree_M x0))) =>
    @MTele_cs S.Type_sort (@mTele nat (fun _ : nat => mBase)) x0
      (internal_meq_rew_r Type
         (to_ty
            (tyTree_FAVal Type
               (fun t : Type =>
                tyTree_FAVal Type
                  (fun t0 : Type =>
                   tyTree_imp (tyTree_M t)
                     (tyTree_imp
                        (tyTree_imp (tyTree_base t) (tyTree_M t0))
                        (tyTree_M t0))))))
         (forall (A B : Type) (_ : t A) (_ : forall _ : A, t B), t B)
         (fun A0 : Type => A0) (@bind)
         (@meq_refl Type
            (forall (A B : Type) (_ : t A) (_ : forall _ : A, t B),
             t B)) x x0 x1 x2))).

Fail Definition test' :=  @bind † [t: (_ : nat)].
