From Mtac2 Require Import Base Mtac2 Sorts MTele MFixDef.
Import Sorts.S.
Import M.notations.
Import M.M.

Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).
Local Notation InF s n := (forall now_ty : forall s0 : Sort, MTele_Sort s0 n -> s0, (forall (s0 : Sort) (T : MTele_Sort s0 n), MTele_val T -> now_ty s0 T) -> s).

(* If recursion is needed then it's TyTree, if not only Type *)
Inductive TyTree : Type :=
| tyTree_val {m : MTele} (T : MTele_Ty m) : TyTree
 | tyTree_M (T : Type) : TyTree
| tyTree_MFA {m : MTele} (T : MTele_Ty m) : TyTree
| tyTree_In (s : Sort) {m : MTele} (F : InF s m) : TyTree
 | tyTree_imp (T : TyTree) (R : TyTree) : TyTree
| tyTree_FATele {m : MTele} (T : MTele_Ty m) (F : forall t : MTele_val T, TyTree) : TyTree
| tyTree_FATele1 {m : MTele} (T : Type) (F : forall t : T, TyTree) : TyTree
 | tyTree_FA (T : Type) (F : T -> TyTree) : TyTree
 | tyTree_FAType (F : Type -> TyTree) : TyTree
 | tyTree_base (T : Type) : TyTree
.

Fixpoint to_ty (X : TyTree) : Type :=
  match X as X' with
  | tyTree_val T => MTele_val T
  | tyTree_M T => M T
  | tyTree_MFA T => MFA T
  | tyTree_In s F => MTele_val (MTele_In s F)
  | tyTree_imp T R => to_ty T -> to_ty R
  | @tyTree_FATele m T F => forall T, to_ty (F T)
  | tyTree_FA T F => forall t : T, to_ty (F t)
  | tyTree_FAType F => forall T : Type, to_ty (F T)
  | tyTree_base T => T
  end.

Definition to_tree (X : Type) : M TyTree :=
  (mfix1 rec (X : Type) : M TyTree :=
    mmatch X as X return M TyTree with
    (* | [? (m : MTele) (T : MTele_Ty m)] MTele_val T =>
       ret (tyTree_val p T) (* fail *) *)
    | [? T : Type] (M T):Type =>
      ret (tyTree_M T)
    (* | [? (m : MTele) (T : MTele_Ty m)] (MFA T):Type =>
      ret (tyTree_MFA T) (* fail *) *)
    | [? T R : Type] T -> R =>
      T <- rec T ;
      R <- rec R;
      ret (tyTree_imp T R)
    (* | [? (m : MTele) (T : MTele_Ty m) (F : forall x : MTele_val T, Type)] forall T , F T =>
      \nu t : _,
        F <- rec (F t) p;
        F <- abs_fun t F;
        ret (tyTree_FATele p T F) (* fail *) *)
    | [? F : Type -> Type] forall T : Type, F T =>
      \nu T : Type,
        F <- rec (F T);
        F <- abs_fun T F;
        ret (tyTree_FAType F)
    | [? T (F : forall t : T, Type)] forall t : T, F t =>
      \nu t : T,
        F <- rec (F t);
        F <- abs_fun t F;
        ret (tyTree_FA T F)
    | _ => ret (tyTree_base X)
    end) X.

Definition to_tree' {X : Type} (x : X) := to_tree X.

(* pol means polarity at that point of the tree *)
(* l means "left" *)
(* We don't want the M at the return type *)
Fixpoint checker (pol : bool) (l : bool) (X : TyTree) : Prop :=
  match X as X' with
  (* direct telescope cases *)
  | tyTree_val T => False
  | tyTree_MFA T => False
  | tyTree_In s F => False
  | @tyTree_FATele m T F => False
  (* non-telescope cases *)
  | tyTree_M T =>
    match andb pol l with
    | true => False
    | false => True
    end
  | tyTree_base T => True
  (* indirect cases *)
  | tyTree_imp T R => and (checker (negb pol) true T) (checker pol false R)
  | tyTree_FA T F => forall t : T, checker pol false (F t)
  | tyTree_FAType F => forall T : Type, checker pol false (F T)
  end.


Goal TyTree.
mrun (to_tree' (@ret)).
Show Proof.

Goal TyTree.
mrun (to_tree'(@bind)).
Show Proof.

Goal TyTree.
mrun (to_tree (forall (m : MTele) (A B : MTele_Ty m), MFA A -> (MTele_val A -> MFA B) -> MFA B)).
Show Proof.

Notation "'[withP' now_ty , now_val '=>' t ]" :=
  (MTele_In (SProp) (fun now_ty now_val => t))
  (at level 0, format "[withP now_ty , now_val => t ]").

Eval compute in (to_ty (tyTree_base nat)).
Eval compute in (to_ty (tyTree_FAType (fun T : Type => tyTree_imp (tyTree_base T) (tyTree_M T)))).

(* This works correctly *)
Eval compute in (checker true false (tyTree_FAType (fun T : Type => tyTree_imp (tyTree_base T) (tyTree_M T)))).
(* Fail because it uses telescopes *)
Eval compute in (checker true false (tyTree_FA MTele
   (fun t0 : MTele =>
    tyTree_FA (MTele_Ty t0)
      (fun t1 : MTele_Ty t0 =>
       tyTree_FA (MTele_Ty t0)
         (fun t2 : MTele_Ty t0 =>
          tyTree_imp (tyTree_MFA t1)
            (tyTree_imp
               (tyTree_imp (tyTree_val t1)
                  (tyTree_MFA t2)) (tyTree_MFA t2))))))).

Definition NotProperType : Exception. exact exception. Qed.

Eval compute in (checker true _ (tyTree_FAType (fun T : Type => tyTree_imp (tyTree_base T) (tyTree_M T)))).

Definition checker' : forall (p : bool) (l : bool) (T : TyTree), M (checker p l T) :=
  mfix3 f (p : bool) (l : bool) (T : TyTree) : M (checker p l T) :=
    mmatch T as T' return M (checker p l T') with
    | [? X] tyTree_base X => ret (I)
    | [? X] tyTree_M X =>
      match p as p' return M (checker p' l (tyTree_M X)) with
      | true =>
        match l as l' return M (checker true l' (tyTree_M X)) with
        | true => M.raise NotProperType
        | false => ret (I)
        end
      | false => ret (I)
      end
    | [? (F : Type -> TyTree)] tyTree_FAType F =>
      \nu X : Type,
        t <- f p false (F X);
        t <- abs_fun (P := fun X : Type => checker p false (F X)) X t;
        ret (t)
    | [? (X : Type) (F : X -> TyTree)] tyTree_FA X F =>
      \nu x : X,
        t <- f p false (F x);
        t <- abs_fun (P := fun x : X => checker p false (F x)) x t;
        ret (t)
    | [? (X Y : TyTree)] tyTree_imp X Y =>
      x <- f (negb p) true X;
      y <- f p false Y;
      ret (conj x y)
    | _ => raise NotProperType
    end.

(** Given an MTele_Ty value and an UNCURRY, it returns the type after applying the values *)
Fixpoint RETURN {s : Sort} {m : MTele} : MTele_Sort s m -> UNCURRY m -> s :=
  match m with
  | mBase => fun T _ => T (* It's the base so only T : MTele_Ty m *)
  | mTele f => fun T '(existT _ x U) => RETURN (T x) U (* U is the rest of the tuple, add a value to T in each step *)
  end.

(** It uncurries an MFA T transforming it to an "UNCURRY" *)
Fixpoint uncurry {m : MTele} :
  forall {T : MTele_Ty m},
  MFA T -> forall U : UNCURRY m, M (@RETURN SType _ T U) :=
  match m as m return
        forall T : MTele_Ty m,
          MTele_val (MTele_C SType SProp M T) -> forall U : UNCURRY m, M (@RETURN SType _ _ U)
  with
  | mBase => fun T F _ => F (* Just return F : MFA T *)
  | mTele f => fun T F '(existT _ x U) => uncurry (F x) U (* Apply x to the MFA T and keep going *)
  end.

(** Same as above, but for MTele_val *)
Fixpoint uncurry_val {s : Sort} {m : MTele} :
  forall {A : MTele_Sort s m},
  MTele_val A -> forall U : UNCURRY m, @RETURN s m A U :=
  match m as m return
        forall A : MTele_Sort s m,
          MTele_val A -> forall U : UNCURRY m, @RETURN s m A U
  with
  | mBase => fun A F _ => F
  | mTele f => fun A F '(existT _ x U) => @uncurry_val s (f x) _ (App F x) _
  end.

Definition uncurry_in {s : Sort} :
  forall {m : MTele} (F : (forall now_ty : (forall s0 : Sort, MTele_Sort s0 m -> s0),
 (forall (s0 : Sort) (T : MTele_Sort s0 m), MTele_val T -> now_ty s0 T) -> s)),
  (MTele_val (MTele_In s F)) ->
  forall U : UNCURRY m, 
    let now_ty := fun (s' : Sort) (ms : MTele_Sort s' m) => RETURN ms U in
    let now_val := fun (s' : Sort) (ms : MTele_Sort s' m) (mv : MTele_val ms) => uncurry_val mv U in
    F now_ty now_val.
  fix IH 1; destruct m; intros.
  + simpl in *. assumption.
  + simpl in *. destruct U. specialize (IH (F x) _ (App X0 x) u). assumption.
Defined.

(** It uncurries an "UNCURRY" transforming it to an MFA T *)
Fixpoint curry_val {s : Sort} {m : MTele} :
  forall {A : MTele_Sort s m},
  (forall U : UNCURRY m, @RETURN s m A U) -> MTele_val A :=
  match m with
  | mBase => fun A F => F tt
  | @mTele T f => fun A F => Fun (fun a : T => curry_val (fun U => F (existT _ a U)))
  end.

Definition ShitHappens : Exception. exact exception. Qed.

Let T := (tyTree_FAType (fun T : Type => tyTree_imp (tyTree_base T) (tyTree_M T))).
Let t : to_ty T := @ret.

Fixpoint lift (m : MTele) (p l : bool) (T : TyTree) : forall (f : to_ty T) (c : checker p l T), M { T : TyTree & to_ty T} :=
  match T as T return forall (f : to_ty T) (c : checker p l T), M { T' : TyTree & to_ty T'} with
  (* | [? X] tyTree_M X => _ *)
  (* | tyTree_imp X Y => *)
  (*   fun f c => *)
  (*     c_x <- checker' (negb p) true (X); *)
  (*     X <- lift m (negb p) true X _ c_x; *)
  (*     _ *)
  (* | tyTree_FA X F => (* Here I should use FATele with curry/uncurry *) *)
  (*   fun f c => *)
  (*    \nu x : X, *)
  (*      c' <- checker' p l (F x); *)
  (*      s <- lift m p l (F x) (f x) c'; *)
  (*      (* p1 <- abs_fun x (Projt1 s); *) *)
  (*      (* p2 <- abs_fun x (projT2 s); *) *)
  (*      \nu tty : MTele_Ty m, *)
  (*      let p1 := tyTree_FA tty (fun v : MTele_val tty => projT1 s) in *)
  (*      let p2 := (fun v : () => projT2 s) in *)
  (*      ret (existT to_ty p1 p2) *)
  | tyTree_FAType F => (* this one is the equivalent to tyTree_FATele, I think *)
    fun f c =>
      c' <- checker' p l (F (MTele_Ty m));
      s <- lift m p l (F (MTele_Ty m)) (f (MTele_Ty m)) c'; (* sigT of continuation *)
      let p1 := tyTree_FATele1 (MTele_Ty m) (projT1 s) in
      let p2 := (projT2 s) in
      let f := fun X : Type => projT2 s in
      ret (existT to_ty (T) (projT2 s))
  (* | [? X] tyTree_base X => *)
  (*   let T := tyTree_base (MTele_Ty m) in *)
  (*   let f : to_ty T = t *)
  (*   existT T *)
  | _ => fun t c => raise ShitHappens
  end.

Check (@mTele nat (fun x : nat => mBase)).

Eval compute in lift (mTele (fun x : nat => mBase)) true false (tyTree_FA )

projT1