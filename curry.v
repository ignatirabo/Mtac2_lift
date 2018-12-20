From Mtac2 Require Import Base Mtac2 Sorts MTele MFixDef.
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
| tyTree_In (s : Sort) {m : MTele} (F : InF s m) : TyTree
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

Fixpoint curry {m : MTele} :
  forall {T : MTele_Ty m},
  (forall U : UNCURRY m, M (RETURN T U)) -> MFA T :=
  match m with
  | mBase => fun T F => F tt
  | mTele f => fun T F x => curry (fun U => F (existT _ x U))
  end.

(** It uncurries an "UNCURRY" transforming it to an MFA T *)
Fixpoint curry_val {s : Sort} {m : MTele} :
  forall {A : MTele_Sort s m},
  (forall U : UNCURRY m, @RETURN s m A U) -> MTele_val A :=
  match m with
  | mBase => fun A F => F tt
  | @mTele T f => fun A F => Fun (fun a : T => curry_val (fun U => F (existT _ a U)))
  end.

Definition ShitHappens : Exception. exact exception. Qed.
Definition UnmagicCase : Exception. exact exception. Qed.

(*** M-check *)

(* Checks if a given type A is found "under M" *)
(* True implies that A is "under M", false otherwise *)
Definition m_check (T : TyTree) (A : Type) : M bool :=
  print "m_check on T:";;
  print_term T;;
  (mfix1 f (T : TyTree) : M bool :=
  mmatch T return M bool with
  | [? X] tyTree_base X => ret false
  | [? X] tyTree_M X =>
    mmatch X return M bool with
    | A => ret true
    | _ => ret false
    end
  | [? X Y] tyTree_imp X Y => fX <- f X;
                             fY <- f Y;
                             let r := orb fX fY in
                             ret r
  | [? F] tyTree_FAType F => print_term (F A);;
                            \nu X : Type,
                            f (F X)
  | _ => ret false
  end) T.

(* Definition test_m_check := ltac:(mrun (m_check (tyTree_M nat) bool false)). *)

(*** Magic section *)

(* Return: big f with accesors and F now_ty now_ty = to_ty T. *)
Let now_ty {m} (U : UNCURRY m) := fun (s' : Sort) (ms : MTele_Sort s' m) => RETURN ms U.
Let now_val {m} (U : UNCURRY m) :=
  fun (s' : Sort) (ms : MTele_Sort s' m) (mv : MTele_val ms) => uncurry_val mv U.

Let magicR {m} (U : UNCURRY m) (T : TyTree) :=
  {F : InF SType m & (to_ty T = F (now_ty U) (now_val U))}.

Definition magic {m : MTele} (U : UNCURRY m) (T : TyTree)
                 (p l : bool) :
                 M (magicR U T) :=
  (mfix3 f (T : TyTree) (p l : bool) : M (magicR U T) :=
    mmatch T as e return M (magicR U e) with
    | [? (A : MTele_Ty m)] tyTree_base (RETURN A U) =>
      print "magic: base";;
      let F : InF SType m := fun nty nval => nty SType A in
      let eq_p : to_ty (tyTree_base (RETURN A U)) = F (now_ty U) (now_val U) := eq_refl in
      ret (existT _ F eq_p)
    | [? (A : MTele_Ty m)] tyTree_M (RETURN A U) =>
      print "magic: M";;
      let F : InF SType m := fun nty nval => M (nty SType A) in
      let eq_p : to_ty (tyTree_M (RETURN A U)) = F (now_ty U) (now_val U) := eq_refl in
      ret (existT _ F eq_p)
    | [? X Y] tyTree_imp X Y =>
      print "magic: imp";;
      ''(existT _ FX pX) <- f X (negb p) true;
      ''(existT _ FY pY) <- f Y p false;
      let F : InF SType m := fun nty nval => (FX nty nval) -> (FY nty nval) in
      let eq_p : to_ty (tyTree_imp X Y) = F (now_ty U) (now_val U) :=
        ltac:(simpl in *; rewrite pX, pY; refine eq_refl) in
      ret (existT _ F eq_p)
    | [? A] tyTree_base A =>
      print "magic: unmagic";;
      let F : InF SType m := fun nty nval => A in
      ret (existT _ F (eq_refl))
    | _ => raise UnmagicCase
    end) T p l.

(*** Lift section *)

Polymorphic Fixpoint lift (m : MTele) (U : UNCURRY m) (p l : bool) (T : TyTree) :
  forall (f : to_ty T) (c : checker p l T), M { T : TyTree & to_ty T} :=
  match T as T return forall (f : to_ty T) (c : checker p l T), M { T' : TyTree & to_ty T'} with
  | tyTree_base X => (* I destruct X *)
    fun f c =>
      print "lift: base";;
      mmatch existT (fun X : Type => (to_ty (tyTree_base X)) *m
                                  checker p l (tyTree_base X) *m UNCURRY m)
                    X
                    (m: f, c, U)
      return M { T' : TyTree & to_ty T'} with
      (*| [? (A : MTele_Ty m)
           (f : to_ty (tyTree_base (RETURN A U)))
           (c : checker p l (tyTree_base (RETURN A U)))]
        existT (fun X : Type => (to_ty (tyTree_base X)) *m
                                checker p l (tyTree_base X) *m UNCURRY m)
               (RETURN A U)
               (m: f, c, U) =>
        let mt_v : MTele_val A := _ in
        ret (existT (fun X : TyTree => to_ty X) (tyTree_val A) mt_v)*)
      | _ => ret (existT (fun X : TyTree => to_ty X) (tyTree_base X) f)
      end
  | tyTree_M X => (* Two cases, one for return value under M, other for any other M *)
    fun f c =>
      print "lift: M";;
      mmatch existT (fun X : Type => (to_ty (tyTree_M X)) *m
                                     checker p l (tyTree_M X))
                    X
                    (m: f, c)
      return M { T' : TyTree & to_ty T'} with
      | [? (A : MTele_Ty m) f c]
        existT (fun X : Type => (to_ty (tyTree_M X) *m checker p l (tyTree_M X)))
               (RETURN A U)
               (m: f, c) =>
          print "I fail here master";;
          print "f:";;
          print_term f;;
          f <- @abs_fun _ (fun U => to_ty (tyTree_M (RETURN A U))) U f;
          let f := curry f in
          ret (existT _ (tyTree_MFA A) f)
      | _ => ret (existT (fun X : TyTree => to_ty X) (tyTree_M X) f)
      end
  | tyTree_imp X Y =>
    fun f c =>
      print "lift: imp";;
      mtry
        (''(existT _ F e) <- magic U X (negb p) true;
        \nu x : MTele_val [WithT now_ty, now_val =>
                           F now_ty now_val],
          (* ltac:(rewrite e in f; exact (f (uncurry_in (s:=SType) F x U))) *)
          (* lift on right side Y *)
          let G := (F (now_ty U) (now_val U)) -> to_ty Y in
          match eq_sym e in _ = T return (T -> to_ty Y) -> M _ with
          | eq_refl => fun f : G =>
            ''(existT _ Y' f) <- lift m U p false (Y) (f (uncurry_in (s:=SType) F x U)) (proj2 c);
            f <- abs_fun x f;
            print "survive1";;
            ret (existT to_ty
                (tyTree_imp (tyTree_In SType F) Y')
                f)
          end f)
      with UnmagicCase =>
        print "UnmagicCase raised";;
        \nu x : to_ty X,
          ''(existT _ Y' f) <- lift m U p false (Y) (f x) (proj2 c);
          f <- abs_fun x f;
          ret (existT to_ty (tyTree_imp X Y') f)
      end
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
      b <- m_check (F A) A;
      if b then
        \nu A : MTele_Ty m,
          let c' : checker p false (F (RETURN A U)):= c (RETURN A U) in
          s <- lift m U p false (F (RETURN A U)) (f (RETURN A U)) c';
          let '(existT _ T' f') := s in
          T'' <- abs_fun (P := fun A => TyTree) A T';
          f' <- coerce f';
          f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
          let T'' := tyTree_FATele1 m T'' in
          print "T'':";;
          print_term T'';;
          print "f'':";;
          print_term f'';;
          ret (existT to_ty T'' f'')
      else
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
  | _ => fun _ _ => print_term T;;
                    raise ShitHappens
  end.

Definition lift' (T : TyTree) (f : to_ty T) : MTele -> M {T : TyTree & to_ty T} :=
  fun (m : MTele) =>
  \nu U : UNCURRY m,
    c <- (checker' true false T);
    lift m U true false T f c.

(*** Examples *)

(** ret *)
(*
Let R := tyTree_FAType (fun A : Type => (tyTree_imp (tyTree_base A) (tyTree_M A))).
Let r : to_ty R := @ret.
Definition mret : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' R r m; abs_fun m l)).

Eval cbn in fun m => projT1 (mret m).
*)

(** bind *)
(*
Let B := (tyTree_FAType (fun A => tyTree_FAType (fun B => tyTree_imp (tyTree_M A) (tyTree_imp (tyTree_imp (tyTree_base A) (tyTree_M B)) (tyTree_M B))))).
Let b : to_ty B := @bind.
Definition mbind : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' B b m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mbind m)).
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

(** nu: fails with exception AbsDependencyError *)
(**)
Let T : TyTree := tyTree_FAType (fun A => tyTree_FAType (fun B => tyTree_imp (tyTree_base name) (tyTree_imp (tyTree_base (moption A)) (tyTree_imp (tyTree_imp (tyTree_base A) (tyTree_M B)) (tyTree_M B))))).
Let t : to_ty T := @nu.
Definition test_m_check := ltac:(mrun (m_check T bool)).
Definition mnu : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T t m; abs_fun m l)).
Eval cbn in fun m => to_ty (projT1 (mnu m)).
*)

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
