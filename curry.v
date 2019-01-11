From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef.
Import Sorts.S.
Import M.notations.
Import M.M.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).
Local Notation InF s n := (forall now_ty : forall s0 : Sort, MTele_Sort s0 n -> s0, (forall (s0 : Sort) (T : MTele_Sort s0 n), MTele_val T -> now_ty s0 T) -> s).

(* If recursion is needed then it's TyTree, if not only Type *)
Inductive TyTree : Type :=
| tyTree_val {m : MTele} (T : MTele_Ty m) : TyTree
| tyTree_M (T : Type) : TyTree
| tyTree_MFA {m : MTele} (T : MTele_Ty m) : TyTree
| tyTree_In (s : Sort) {m : MTele} (F : accessor m -> s) : TyTree
| tyTree_imp (T : TyTree) (R : TyTree) : TyTree
| tyTree_FATele {m : MTele} (T : MTele_Ty m) (F : forall t : MTele_val T, TyTree) : TyTree
| tyTree_FATele1 (m : MTele) (F : forall (T : MTele_Ty m), TyTree) : TyTree
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
  | tyTree_FATele1 m F => forall T : (MTele_Ty m), to_ty (F T)
  | tyTree_FA T F => forall t : T, to_ty (F t)
  | tyTree_FAType F => forall T : Type, to_ty (F T)
  | tyTree_base T => T
  end.

Definition to_tree (X : Type) : M TyTree :=
  (mfix1 rec (X : Type) : M TyTree :=
    mmatch X as X return M TyTree with
    | [? T : Type] (M T):Type =>
      ret (tyTree_M T)
    | [? T R : Type] T -> R => (* no dependency of T on R. It's equivalent to forall _ : T, R *)
      T <- rec T ;
      R <- rec R;
      ret (tyTree_imp T R)
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
    (* | [? (m : MTele) (T : MTele_Ty m)] MTele_val T =>
       ret (tyTree_val p T) (* fail *) *)
    (* | [? (m : MTele) (T : MTele_Ty m)] (MFA T):Type =>
      ret (tyTree_MFA T) (* fail *) *)
    (* | [? (m : MTele) (T : MTele_Ty m) (F : forall x : MTele_val T, Type)] forall T , F T =>
      \nu t : _,
        F <- rec (F t) p;
        F <- abs_fun t F;
        ret (tyTree_FATele p T F) (* fail *) *)
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
  | tyTree_FATele1 m F => False
  (* non-telescope cases *)
  | tyTree_M T =>
    match andb pol l with
    | true => True
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
Show Proof. Qed.

Goal TyTree.
mrun (to_tree' (@bind)).
Show Proof. Qed.

Goal TyTree.
mrun (to_tree (forall (m : MTele) (A B : MTele_Ty m), MFA A -> (MTele_val A -> MFA B) -> MFA B)).
Show Proof. Qed.

(*
Notation "'[withP' now_ty , now_val '=>' t ]" :=
  (MTele_In (SProp) (fun now_ty now_val => t))
  (at level 0, format "[withP now_ty , now_val => t ]").
*)

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
        | true => ret I
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

(** Same as above, but for MTele_val *)
Fixpoint uncurry_val {s : Sort} {m : MTele} :
  forall {A : MTele_Sort s m},
  MTele_val A -> forall U : ArgsOf m, @apply_sort s m A U :=
  match m as m return
        forall A : MTele_Sort s m,
          MTele_val A -> forall U : ArgsOf m, @apply_sort s m A U
  with
  | mBase => fun A F _ => F
  | mTele f => fun A F '(mexistT _ x U) => @uncurry_val s (f x) _ (App F x) _
  end.


Definition uncurry_in_acc {m : MTele} (U : ArgsOf m) : accessor m :=
  let now_const := fun (s : Sort) (T : s) (ms : MTele_Const T m) => apply_const ms U in
  let now_val := fun (s : Sort) (ms : MTele_Sort s m) (mv : MTele_val ms) => uncurry_val mv U in
  Accessor _ now_const now_val.

Definition uncurry_in {s : Sort} :
  forall {m : MTele} (F : accessor m -> s),
  (MTele_val (MTele_In s F)) ->
  forall U : ArgsOf m,
    F (uncurry_in_acc U).
  fix IH 1; destruct m; intros.
  + simpl in *. assumption.
  + simpl in *. destruct U. specialize (IH (F x) _ (App X0 x) a). assumption.
Defined.

(** It uncurries an "UNCURRY" transforming it to an MFA T *)
Fixpoint curry_val {s : Sort} {m : MTele} :
  forall {A : MTele_Sort s m},
  (forall U : ArgsOf m, @apply_sort s m A U) -> MTele_val A :=
  match m with
  | mBase => fun A F => F tt
  | @mTele T f => fun A F => Fun (fun a : T => curry_val (fun U => F (mexistT _ a U)))
  end.

Fixpoint MTele_Cs {s : Sort} (n : MTele) (T : s) : MTele_Sort s n :=
  match n as n return MTele_Sort s n with
  | mBase =>
    T
  | @mTele X F =>
    fun x : X => @MTele_Cs s (F x) T
  end.

Fixpoint MTele_cs {s : Sort} {n : MTele} {X : Type} (f : M X) : MFA (@MTele_Cs SType n X) :=
  match n as n return MFA (@MTele_Cs SType n X) with
  | mBase =>
    f
  | @mTele Y F =>
    (* Fun (fun x : X => @MTele_cs _ (F x) _ f) *)
    @Fun SType Y (fun y : Y => MFA (@MTele_Cs SType (F y) X)) (fun y : Y => @MTele_cs s (F y) X f)
    (* ltac:(simpl in *; refine (@Fun s X (fun x => MTele_val (@MTele_Cs _ (F x) T)) (fun x : X => @MTele_cs _ (F x) T f))) *)
  end.

(* Next line needs to after MTele_cs, if not, Coq fails to typecheck *)
Arguments MTele_Cs {s} {n} _.

(*** Is-M *)

(* Checks if a given type A is found "under M" *)
(* true iff A is "under M", false otherwise *)
Definition is_m (T : TyTree) (A : Type) : M bool :=
  print "is_m on T:";;
  print_term T;;
  (mfix1 f (T : TyTree) : M bool :=
  mmatch T return M bool with
  | [? X] tyTree_base X => ret false
  | [? X] tyTree_M X =>
    mmatch X return M bool with
    | A => ret true
    | _ => ret false
    end
  | [? X Y] tyTree_imp X Y =>
    fX <- f X;
    fY <- f Y;
    let r := orb fX fY in
    ret r
  | [? F] tyTree_FAType F =>
    print_term (F A);;
    \nu X : Type,
    f (F X)
  | [? X F] tyTree_FA X F =>
    \nu x : X,
      f (F x)
  | _ => ret false
  end) T.

Definition contains_u (m : MTele) (U : ArgsOf m) (T : TyTree) : M bool :=
  mtry
    T' <- abs_fun U T;
    print "T' on contains_u:";;
    print_term T';;
    mmatch T' with
    | [? T''] (fun _ => T'') =>
      ret false
    | _ =>
      ret true
    end
  with AbsDependencyError =>
    ret true
  end.

Definition test_is_m := ltac:(mrun (is_m (tyTree_M bool) nat)).

(*** Lift In section *)

Definition ShitHappens : Exception. exact exception. Qed.
Definition UnLiftInCase : Exception. exact exception. Qed.

(* Return: big f with accesors and F now_ty now_ty = to_ty T. *)
(*
Let now_ty {m} (U : ArgsOf m) := fun (s' : Sort) (ms : MTele_Sort s' m) => apply_sort ms U.
Let now_val {m} (U : ArgsOf m) :=
  fun (s' : Sort) (ms : MTele_Sort s' m) (mv : MTele_val ms) => uncurry_val mv U.
*)

Definition lift_inR {m} (T : TyTree) (A : accessor m):=
  {F : (accessor m -> SType) & (to_ty T = F A)}.


Definition lift_in {m : MTele} (U : ArgsOf m) (T : TyTree)
                 (p l : bool) :
                 M (lift_inR T (uncurry_in_acc U)) :=
  (mfix3 f (T : TyTree) (p l : bool) : M (lift_inR T (uncurry_in_acc U)) :=
    mmatch T as e return M (lift_inR e _) with
    | [? (A : MTele_Ty m)] tyTree_base (apply_sort A U) =>
      print "lift_in: base";;
      let F : (accessor m -> Type) := fun a => a.(acc_sort) A in
      let eq_p : to_ty (tyTree_base (apply_sort A U)) = F (uncurry_in_acc U) := eq_refl in
      ret (existT _ F eq_p)
    | [? (A : MTele_Ty m)] tyTree_M (apply_sort A U) =>
      print "lift_in: M";;
      let F : (accessor m -> Type) := fun a => M (a.(acc_sort) A) in
      let eq_p : to_ty (tyTree_M (apply_sort A U)) = F (uncurry_in_acc U) := eq_refl in
      ret (existT _ F eq_p)
    | [? X Y] tyTree_imp X Y =>
      print "lift_in: imp";;
      ''(existT _ FX pX) <- f X (negb p) true;
      ''(existT _ FY pY) <- f Y p false;
      let F := fun a => FX a -> FY a in
      let eq_p : to_ty (tyTree_imp X Y) = F (uncurry_in_acc U) :=
        ltac:(simpl in *; rewrite pX, pY; refine eq_refl) in
      ret (existT _ F eq_p)
    | _ => raise UnLiftInCase
    end) T p l.

(*** Lift section *)

(* p and l represent "polarity" and "left part of implication" *)
Polymorphic Fixpoint lift (m : MTele) (U : ArgsOf m) (p l : bool) (T : TyTree) :
  forall (f : to_ty T) (c : checker p l T), M { T : TyTree & to_ty T} :=
  match T as T return forall (f : to_ty T) (c : checker p l T), M { T' : TyTree & to_ty T'} with
  | tyTree_base X =>
    fun f c =>
      print "lift: base";;
      mmatch existT (fun X : Type => (to_ty (tyTree_base X)) *m
                                  checker p l (tyTree_base X) *m ArgsOf m)
                    X
                    (m: f, c, U)
      return M { T' : TyTree & to_ty T'} with
      | _ => ret (existT (fun X : TyTree => to_ty X) (tyTree_base X) f)
      end
  | tyTree_M X =>
    fun f c =>
      print "lift: M";;
      mmatch existT (fun X : Type => (to_ty (tyTree_M X)) *m
                                     checker p l (tyTree_M X))
                    X
                    (m: f, c)
      return M { T' : TyTree & to_ty T'} with
      | [? (A : MTele_Ty m) f c]
        existT (fun X : Type => (to_ty (tyTree_M X) *m checker p l (tyTree_M X)))
               (apply_sort A U)
               (m: f, c) =>
          print "T:";;
          print_term (to_ty T);;
          print "f:";;
          print_term f;;
          f <- @abs_fun (ArgsOf m) (fun U => to_ty (tyTree_M (apply_sort A U))) U f;
          print "survive2";;
          let f := curry f in
          ret (existT _ (tyTree_MFA A) f)
      | _ =>
        let T := @MTele_Cs SType m X in (* okay *)
        let f' := @MTele_cs SType m X f in
        ret (existT (fun X : TyTree => to_ty X) (tyTree_MFA T) f')
      end
  | tyTree_imp X Y =>
    fun f c =>
      print "lift: imp";;
      print "X on imp:";;
      print_term X;;
      b <- contains_u m U X;
      print "b on imp:";;
      print_term b;;
      if b then
        mtry
          (''(existT _ F e) <- lift_in U X (negb p) true;
          \nu x : MTele_val (MTele_In SType F),
            (* ltac:(rewrite e in f; exact (f (uncurry_in (s:=SType) F x U))) *)
            (* lift on right side Y *)
            let G := (F (uncurry_in_acc U)) -> to_ty Y in
            match eq_sym e in _ = T return (T -> to_ty Y) -> M _ with
            | eq_refl => fun f : G =>
              ''(existT _ Y' f) <- lift m U p false (Y) (f (uncurry_in (s:=SType) F x U)) (proj2 c);
              f <- abs_fun x f;
              print "survive1";;
              ret (existT to_ty
                  (tyTree_imp (tyTree_In SType F) Y')
                  f)
            end f)
        with UnLiftInCase =>
          mfail "UnLiftInCase raised"
        end
      else
        (* Because X does not contain monadic stuff it's assumed it's "final" *)
        \nu x : to_ty X,
          ''(existT _ Y' f) <- lift m U p false (Y) (f x) (proj2 c);
          f <- abs_fun x f;
          ret (existT to_ty (tyTree_imp X Y') f)
  | tyTree_FA X F =>
    fun f c =>
      print "lift: FA";;
      \nu x : X,
       c' <- checker' p l (F x);
       ''(existT _ F f) <- lift m U p l (F x) (f x) c';
       F <- abs_fun x F;
       f <- coerce f;
       f <- abs_fun x f;
       ret (existT _ (tyTree_FA X F) (f))
  | tyTree_FAType F =>
    fun f c =>
      print "lift: FAType";;
      \nu A : Type,
      b <- is_m (F A) A;
      if b then (* Replace A with a (RETURN A U) *)
        \nu A : MTele_Ty m,
          let c' : checker p false (F (apply_sort A U)):= c (apply_sort A U) in
          s <- lift m U p false (F (apply_sort A U)) (f (apply_sort A U)) c';
          let '(existT _ T' f') := s in
          T'' <- abs_fun (P := fun A => TyTree) A T';
          f' <- coerce f';
          f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
          let T'' := tyTree_FATele1 m T'' in
          print "T'':";;
          print_term (to_ty T'');;
          print "f'':";;
          print_term f'';;
          ret (existT to_ty T'' f'')
      else (* A is not monadic, no replacement *)
        let c' : checker p false (F A) := c A in
        s <- lift m U p false (F A) (f A) c';
        let '(existT _ T' f') := s in
        T'' <- abs_fun (P := fun A => TyTree) A T';
        f' <- coerce f';
        f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
        let T'' := tyTree_FAType T'' in
        print "T'':";;
        print_term T'';;
        print "f'':";;
        print_term f'';;
        ret (existT to_ty T'' f'')
  | _ => fun _ _ =>
    print_term T;;
    raise ShitHappens
  end.

Definition lift' (T : TyTree) (f : to_ty T) : MTele -> M {T : TyTree & to_ty T} :=
  fun (m : MTele) =>
  \nu U : ArgsOf m,
    c <- (checker' true false T);
    lift m U true false T f c.

(*** Examples *)

(** ret *)
Let R := tyTree_FAType (fun A : Type => (tyTree_imp (tyTree_base A) (tyTree_M A))).
Let r : to_ty R := @ret.
Definition mret : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' R r m; abs_fun m l)).
Eval cbn in fun m => projT1 (mret m).

(** random nat function *)
Let T := tyTree_imp (tyTree_base nat) (tyTree_imp (tyTree_base nat) (tyTree_base nat)).
Let t : to_ty T := @plus.
Definition mplus : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T t m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mplus m)).

(** bind *)
Let B := (tyTree_FAType (fun A => tyTree_FAType (fun B => tyTree_imp (tyTree_M A) (tyTree_imp (tyTree_imp (tyTree_base A) (tyTree_M B)) (tyTree_M B))))).
Let b : to_ty B := @bind.
Definition mbind : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' B b m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mbind m)).

(** Actual attemp idea *)
(*
a <- f x;
*)

(** mtry' *)
(*
Let T : TyTree := tyTree_FAType (fun A => tyTree_imp (tyTree_M A) (tyTree_imp (tyTree_imp (tyTree_base Exception) (tyTree_M A)) (tyTree_M A))).
Let t : to_ty T := @mtry'.
Definition mtry'' : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T t m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mtry'' m)).
*)

(** raise' *)
(*
Let T : TyTree := tyTree_FAType (fun A => tyTree_imp (tyTree_base Exception) (tyTree_M A)).
Let t : to_ty T := @raise'.
Definition mraise' : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T t m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mraise' m)).
*)

(** is_var *)
(*
(* Does nothing to the function, which is correct in this case *)
Let B : TyTree := tyTree_FAType (fun A => tyTree_imp (tyTree_base A) (tyTree_M bool)).
Let b : to_ty B := @is_var.
Definition mis_var : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' B b m; abs_fun m l)).

Eval cbn in fun m => projT1 (mis_var m).
*)

(** nu *)
(*
Let T : TyTree := tyTree_FAType (fun A => tyTree_FAType (fun B => tyTree_imp (tyTree_base name) (tyTree_imp (tyTree_base (moption A)) (tyTree_imp (tyTree_imp (tyTree_base A) (tyTree_M B)) (tyTree_M B))))).
Let t : to_ty T := @nu.
Definition mnu : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T t m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mnu m)).
*)

(** nu_let *)
(*
Let T : TyTree := tyTree_FAType (fun A => tyTree_FAType (fun B => tyTree_FAType (fun C => tyTree_imp (tyTree_base name) (tyTree_imp (tyTree_base C) (tyTree_imp (tyTree_imp (tyTree_base A) (tyTree_imp (tyTree_base C) (tyTree_M B))) (tyTree_M B)))))).
Let t : to_ty T := @nu_let.
Definition mnu_let : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T t m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mnu_let m)).
*)

(** abs_fun: problem is using lift_in. Can be solved in two ways: not being in the domain of the function (modifying checker) or by being able to not call lift_in *)
(* Calling lift_in makes it so that U is still used and then it's never abstracted *)
Let T_abs : TyTree := tyTree_FAType (fun A => tyTree_FA (A -> Type) (fun P : A -> Type => tyTree_FA A (fun x => tyTree_imp (tyTree_base (P x)) (tyTree_M (forall x : A, P x))))).
Let t_abs : to_ty T_abs := @abs_fun.
Definition mabs_fun : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T_abs t_abs m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mabs_fun m)).



(*** Garbage collector *)
(*
Let testfT := tyTree_FAType (fun A => tyTree_FA A (fun a => tyTree_M (a = a))).
Let testf : to_ty testfT := fun A a => ret (eq_refl).
Definition testfl := ltac:(mrun (\nu m : MTele, l <- lift' testfT testf m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (testfl m)).
*)

(* Trying lift on a function which shouldn't work. *)
(*
Let F := tyTree_FAType (fun A => tyTree_FAType (fun (B : A -> Type) =>
  tyTree_imp
   (tyTree_imp
     (tyTree_FA A (fun a => tyTree_M (B x)))
     (tyTree_FA A (fun a => tyTree_M (B x))))
   (tyTree_FA A (fun a => tyTree_M (B x))))).
Let f : to_ty F := @mfix1.

Definition mfix : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' F f m; abs_fun m l)).
*)

(*
Definition fix0 : forall (B : Type), (M B -> M B) -> M B :=
  fun B f =>
    @fix1 unit (fun _ => B) (fun g => g) tt.

Let fix0_tree := tyTree_FAType (fun A => tyTree_imp (tyTree_imp (tyTree_M A) (tyTree_M A)) (tyTree_M A)).
Let fix0_iso : to_ty fix0_tree := @fix0.

Definition mfix : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' fix0_tree fix0_iso m; abs_fun m l)).
Eval cbn in fun m => projT1 (mfix m).
*)

(* mmatch existT (fun P : { X : Type & (X -> TyTree)} => (to_ty (tyTree_FA (projT1 P) (projT2 P))) *m checker p l (tyTree_FA (projT1 P) (projT2 P)))
                    (existT _ X F)
                    (m: f, c)
      return M { T' : TyTree & to_ty T'} with
      | [? (A : MTele_Ty m)] existT (fun P : { X : Type & (X -> TyTree)} =>(to_ty (tyTree_FA (projT1 P) (projT2 P))) *m checker p l (tyTree_FA (projT1 P) (projT2 P)))
      (existT _ (repl A) F)
      (m: f, c) =>
        _
      | _ => ret (existT (fun X : TyTree => to_ty X) (tyTree_FA X F) f)
      end
*)
