From Mtac2 Require Import Mtac2 MTele  meta.MTeleMatch meta.MFix.


Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

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

Notation "[t: a .. b ]" := (mTele (fun a => .. (mTele (fun b => mBase)) ..))
  (a binder, b binder, at level 0).

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

Definition unfold_type_of {A} (c: A) :=
  let T := dreduce (@type_of) (type_of c) in
  M.dbg_term "T: " T;;
  M.ret T.
Notation "'ty_of' x" := (ltac:(mrun (unfold_type_of x))) (at level 0).

Print Module M.M.


Notation "d † m" := (
  let c := d in 
  ltac:(
  let C := constr:(ltac: (mrun (unfold_type_of c))) in
  let tA := constr:(ltac: (mrun (to_tree C))) in
  let lfted := constr:(ltac: (mrun (@lift' tA c m))) in
  exact (mprojT2 lfted)
  )
) (at level 50).


Definition test' :=  Eval simpl in @bind † [t: (a:nat)].
Definition test'' (S:Set) := 
  Eval simpl in (@bind † [t: (l:list S) (_ : l <> nil)]).
Definition test''' (S:Set) := 
  Eval simpl in (max S † [t: (l:list S) (_ : l <> nil)]).

Definition test'''' (S: Set) (X:Type) : ((forall l, l <> nil -> (S -> S -> S) -> M X) -> forall l:list S, l <> nil -> M X) :=
  test'' S _ _ (test''' S).


Definition list_max (S: Set) : forall l:list S, l <> nil -> M S :=
  (@bind † [t: (l: list S) (H: l <> nil)]) _ _ 
    (max S † [t: (l:list S) (_ : l <> nil)])
  (fun l (H: l <> nil) (max : S -> S -> S) =>
  (mfix2 f (l: list S) (H : l <> nil) : M S :=
    (mtmmatch l as l' return l' <> nil -> M S with
    | [? e] [e] =m> M.ret e † [t: (_ : [e] <> nil)]
    | [? e1 e2 l'] (e1 :: e2 :: l') =m> fun nonE =>
      let m := max e1 e2 in
      f (m :: l') cons_not_nil
    end) H) l H).

Eval compute in ltac:(mrun (list_max nat [1;2;3;2] cons_not_nil)).
