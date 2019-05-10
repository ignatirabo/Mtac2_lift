From Mtac2 Require Import Base Mtac2 Specif Sorts MTele MFixDef MTeleMatch.
Import Sorts.S.
Import M.notations.
Import M.M.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Unset Printing Universes.

Local Definition MFA {n} (T : MTele_Ty n) := (MTele_val (MTele_C SType SProp M T)).
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
      T <- rec T;
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


Definition NotEqualTree : Exception. exact exception. Qed.

Definition tytree_imp_eq : forall (L R : Type) (L' R' : TyTree) (EL : L =m= to_ty L') (ER : R =m= to_ty R'), (L -> R) =m= (to_ty (tyTree_imp L' R')).
Proof.
  intros. rewrite EL. rewrite ER. simpl. reflexivity.
Defined.

(*
Definition tytree_fa_eq : forall (T : Type) (F : T -> Type) (F' : TyTree) (EF : F =m= to_ty F'), (forall t : T, F t) =m= (to_ty ) 
*)

(*
Definition tytree_fat_eq : forall (T : Type) (F : Type -> Type) (F' : TyTree) (F'' : Type -> TyTree) (EF : F T =m= to_ty F') (EF' : F' =m= F'' T), F T =m= (to_ty (F'' T)).
Proof.
  intros. rewrite EF. rewrite EF'. reflexivity.

Definition abs_fun_eq: forall{A: Type} {P: A->Type} (x: A) (t: P x),
  M m:{t': forall x, P x & t' x =m= t}.
  constructor. Qed.

Program Definition to_tree (X : Type) : M m:{ T : TyTree & X =m= (to_ty T) } :=
  (mfix1 rec (X : Type) : M m:{ T : TyTree & X =m= (to_ty T) } :=
    mmatch X as X return M m:{ T : TyTree & X =m= (to_ty T) } with
    | [? T : Type] (M T):Type =>
      ret (mexistT _ (tyTree_M T) meq_refl)
    | [? L R : Type] L -> R => 
      ''(mexistT _ L' EL) <- rec L;
      ''(mexistT _ R' ER) <- rec R;
      let T : TyTree := (tyTree_imp L' R') in
      let E := tytree_imp_eq L R L' R' EL ER in
      ret (mexistT _ T E)
    | [? T (F : forall t : T, Type)] forall t : T, F t =>
      \nu t : T,
        ''(mexistT _ F' EF) <- rec (F t);
        ''(mexistT _ F'' EF') <- abs_fun_eq t F';
        let E : (forall t : T, F t) =m= to_ty (tyTree_FA T F'') := _ in
        ret (mexistT _ (tyTree_FA T F'') E)
    (*
    | [? F : Type -> Type] forall T : Type, F T =>
      \nu T : Type,
        ''(mexistT _ F' EF) <- rec (F T);
        F'' <- abs_fun T F';
        let E : (forall T : Type, F T) =m= to_ty (tyTree_FAType F'') := _ in
        ret (mexistT _ (tyTree_FAType F'') E)
    *)
    (*
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
    *)
    end) X.
Next Obligation.
*)


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
  m:{F : (accessor m -> SType) & (to_ty T = F A)}.


Definition lift_in {m : MTele} (U : ArgsOf m) (T : TyTree)
                 (p l : bool) :
                 M (lift_inR T (uncurry_in_acc U)) :=
  (mfix3 f (T : TyTree) (p l : bool) : M (lift_inR T (uncurry_in_acc U)) :=
    mmatch T as e return M (lift_inR e _) with
    | [? (A : MTele_Ty m)] tyTree_base (apply_sort A U) =>
      print "lift_in: base";;
      let F : (accessor m -> Type) := fun a => a.(acc_sort) A in
      let eq_p : to_ty (tyTree_base (apply_sort A U)) = F (uncurry_in_acc U) := eq_refl in
      ret (mexistT _ F eq_p)
    | [? (A : MTele_Ty m)] tyTree_M (apply_sort A U) =>
      print "lift_in: M";;
      let F : (accessor m -> Type) := fun a => M (a.(acc_sort) A) in
      let eq_p : to_ty (tyTree_M (apply_sort A U)) = F (uncurry_in_acc U) := eq_refl in
      ret (mexistT _ F eq_p)
    | [? X Y] tyTree_imp X Y =>
      print "lift_in: imp";;
      ''(mexistT _ FX pX) <- f X (negb p) true;
      ''(mexistT _ FY pY) <- f Y p false;
      let F := fun a => FX a -> FY a in
      let eq_p : to_ty (tyTree_imp X Y) = F (uncurry_in_acc U) :=
        ltac:(simpl in *; rewrite pX, pY; refine eq_refl) in
      ret (mexistT _ F eq_p)
    | _ => raise UnLiftInCase
    end) T p l.

(*** Lift section *)

(* p and l represent "polarity" and "left part of implication" *)
Polymorphic Fixpoint lift (m : MTele) (U : ArgsOf m) (p l : bool) (T : TyTree) :
  forall (f : to_ty T), M m:{ T : TyTree & to_ty T} :=
  match T as T return forall (f : to_ty T), M m:{ T' : TyTree & to_ty T'} with
  | tyTree_base X =>
    fun f =>
      print "lift: base";;
      mmatch mexistT (fun X : Type => to_ty (tyTree_base X)) X f
      return M m:{ T' : TyTree & to_ty T'} with
      | _ => ret (mexistT (fun X : TyTree => to_ty X) (tyTree_base X) f)
      end
  | tyTree_M X =>
    fun f =>
      print "lift: M";;
      mmatch mexistT (fun X : Type => to_ty (tyTree_M X)) X f
      return M m:{ T' : TyTree & to_ty T'} with
      | [? (A : MTele_Ty m) f]
        mexistT (fun X : Type => to_ty (tyTree_M X))
               (apply_sort A U)
               f =>
          print "T:";;
          print_term (to_ty T);;
          print "f:";;
          print_term f;;
          f <- @abs_fun (ArgsOf m) (fun U => to_ty (tyTree_M (apply_sort A U))) U f;
          print "survive2";;
          let f := curry f in
          ret (mexistT _ (tyTree_MFA A) f)
      | _ =>
        (* Constant case *)
        let T := @MTele_Cs SType m X in (* okay *)
        let f' := @MTele_cs SType m X f in
        ret (mexistT (fun X : TyTree => to_ty X) (tyTree_MFA T) f')
      end
  | tyTree_imp X Y =>
    fun f =>
      print "lift: imp";;
      print "X on imp:";;
      print_term X;;
      b <- contains_u m U X;
      print "b on imp:";;
      print_term b;;
      if b then
        mtry
          (''(mexistT _ F e) <- lift_in U X (negb p) true;
          \nu x : MTele_val (MTele_In SType F),
            (* ltac:(rewrite e in f; exact (f (uncurry_in (s:=SType) F x U))) *)
            (* lift on right side Y *)
            let G := (F (uncurry_in_acc U)) -> to_ty Y in
            match eq_sym e in _ = T return (T -> to_ty Y) -> M _ with
            | eq_refl => fun f =>
              ''(mexistT _ Y' f) <- lift m U p false (Y) (f (uncurry_in (s:=SType) F x U));
              f <- abs_fun x f;
              print "survive1";;
              ret (mexistT to_ty
                  (tyTree_imp (tyTree_In SType F) Y')
                  f)
            end f)
        with UnLiftInCase =>
          mfail "UnLiftInCase raised"
        end
      else
        (* Because X does not contain monadic stuff it's assumed it's "final" *)
        \nu x : to_ty X,
          ''(mexistT _ Y' f) <- lift m U p false (Y) (f x);
          f <- abs_fun x f;
          ret (mexistT to_ty (tyTree_imp X Y') f)
  | tyTree_FA X F =>
    fun f =>
      print "lift: FA";;
      \nu x : X,
       ''(mexistT _ F f) <- lift m U p l (F x) (f x);
       F <- abs_fun x F;
       f <- coerce f;
       f <- abs_fun x f;
       ret (mexistT _ (tyTree_FA X F) (f))
  | tyTree_FAType F =>
    fun f =>
      print "lift: FAType";;
      \nu A : Type,
      b <- is_m (F A) A;
      if b then (* Replace A with a (RETURN A U) *)
        \nu A : MTele_Ty m,
          s <- lift m U p false (F (apply_sort A U)) (f (apply_sort A U));
          let '(mexistT _ T' f') := s in
          T'' <- abs_fun (P := fun A => TyTree) A T';
          f' <- coerce f';
          f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
          let T'' := tyTree_FATele1 m T'' in
          print "T'':";;
          print_term (to_ty T'');;
          print "f'':";;
          print_term f'';;
          ret (mexistT to_ty T'' f'')
      else (* A is not monadic, no replacement *)
        s <- lift m U p false (F A) (f A);
        let '(mexistT _ T' f') := s in
        T'' <- abs_fun (P := fun A => TyTree) A T';
        f' <- coerce f';
        f'' <- abs_fun (P := fun A => to_ty (T'' A)) A f';
        let T'' := tyTree_FAType T'' in
        print "T'':";;
        print_term T'';;
        print "f'':";;
        print_term f'';;
        ret (mexistT to_ty T'' f'')
  | _ => fun _ =>
    print_term T;;
    raise ShitHappens
  end.

Definition lift' {T : TyTree} (f : to_ty T) : MTele -> M m:{T : TyTree & to_ty T} :=
  fun (m : MTele) =>
  \nu U : ArgsOf m,
    c <- (checker' true false T);
    lift m U true false T f.

(*** Examples *)


(** mmatch' *)
Let mmatch'_t := tyTree_FAType (fun A : Type => tyTree_FA (A -> Type) (fun P => (tyTree_imp (tyTree_base Exception) (tyTree_FA A (fun y => tyTree_imp (tyTree_base (mlist (branch M A P y))) (tyTree_M (P y))))))).
Let mmatch'_v : to_ty mmatch'_t := @mmatch'.
Definition m_mmatch' (m : MTele) : m:{T : TyTree & to_ty T} := ltac:(mrun (lift' mmatch'_v m)).
Eval cbn in fun m => mprojT1 (m_mmatch' m).

(** ret *)
Let R := tyTree_FAType (fun A : Type => (tyTree_imp (tyTree_base A) (tyTree_M A))).
Let r : to_ty R := @ret.
Definition mret (m : MTele): m:{T : TyTree & to_ty T} := ltac:(mrun (lift' r m)).
Eval cbn in fun m => mprojT2 (mret m).

(** random nat function *)
Let T := tyTree_imp (tyTree_base nat) (tyTree_imp (tyTree_base nat) (tyTree_base nat)).
Let t : to_ty T := @plus.
Definition mplus : MTele -> m:{T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' t m; abs_fun m l)).
Eval cbn in fun m => to_ty (mprojT1 (mplus m)).

(** bind *)
Let B := (tyTree_FAType (fun A => tyTree_FAType (fun B => tyTree_imp (tyTree_M A) (tyTree_imp (tyTree_imp (tyTree_base A) (tyTree_M B)) (tyTree_M B))))).
Let b : to_ty B := @bind.
Definition mbind : MTele -> m:{T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' b m; abs_fun m l)).
Eval cbn in fun m => to_ty (mprojT1 (mbind m)).

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
Definition mabs_fun : MTele -> m:{T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' t_abs m; abs_fun m l)).
Eval cbn in fun m => to_ty (mprojT1 (mabs_fun m)).

(** print *)
(* Calling lift_in makes it so that U is still used and then it's never abstracted *)
Let T_print : TyTree := tyTree_imp (tyTree_base (String.string)) (tyTree_M unit).
Let t_print : to_ty T_print := @print.
(* Definition mprint : MTele -> {T : TyTree & to_ty T} := ltac:(mrun (\nu m : MTele, l <- lift' T_print t_print m; abs_fun m l)). *)
Definition lift_print (m : MTele) : m:{T : TyTree & to_ty T} := ltac:(mrun (lift' t_print m)).
Definition mprint m := mprojT2 (lift_print m).
(* Eval cbn in fun m => to_ty (projT1 (mprint m)). *)

(** Using MTeleMatch and lifted print *)
(*
The type of print is
print : String.string -> M unit
With the lift function we generalize this type to
new_print : forall x : bool,/ String.string -> M unit
The `forall x : bool` is added by lift with the telescope
n := (mTele (fun b : bool => mBase))
*)

(*
Definition test1 : forall x : bool, M unit :=
  mtmmatch true as b return forall x, M unit with
  | _ =>
    mprint (mTele (fun b : bool => mBase)) "MYPRINT3"
  end.

Definition test1_run := ltac:(mrun (test1 true)).
*)

(*
This is the same example without using mtmmatch because it really doesn't change anything
We can check on the *coq* buffer for the message "[DEBUG] MYPRINT2"
*)

(*
Definition bla_new (T : Type) : T -> M {T' : Type & T'} :=
  mtmmatch T as T' return forall x : T', M {T' : Type & T'} with
  | (bool:Type) =u>
    fun f =>
      ret (existT _ (bool:Type) f)
  | _ =u>
    fun f =>
      ret (existT _ T f)
  end.

Definition bla_wot (T : Type) : T -> M T :=
  mtmmatch T as T' return forall x : T', M T' with
  | (bool:Type) =u>
    fun f =>
      ret f
  end.
*)

(*
Definition bla_new1 (T : Type) : T -> M {T' : Type & T'} :=
  mtmmatch T as T' return forall x : T', M {T' : Type & T'} with
  | (bool:Type) =u>
    print "It's a bool!";;
    fun f =>
      ret (existT _ (bool:Type) f)
  | _ =u>
    fun f =>
      ret (existT _ T f)
  end.
*)

(*
- Typeclasses, builds the telescope to match the expected type. 
- Notation to trigger Mtac 
*)

(*
(* This is an example of the problem *)
Fail Definition bla (T : Type) : T -> M {T' : Type & T'} :=
  fun f =>
    mmatch T return M {T' : Type & T'} with
    | (bool:Type) => ret (existT (fun T : Type => T) (bool:Type) f)
    | _ => ret (existT _ T f)
    end.

Definition bla (T : Type) : T -> M {T' : Type & T'} :=
  fun f =>
    mmatch (existT (fun T : Type => T) T f) as T' return M {T : Type & T} with
    | [? (v : bool)] existT (fun T : Type => T) (bool:Type) v => ret (existT (fun T : Type => T) (bool:Type) v)
    | _ => ret (existT _ T f)
    end.
*)

(* Turns a Coq proposition to it's telescope equivalent *)
(* MTele_of should be a certifying: *)
(*
Definition MTele_of (T : Type) : M ( m:{n : MTele & MTele_Ty n} ) :=
    (mfix1 f (T : Type) : M (msigT MTele_Ty) :=
      mmatch T return M (msigT MTele_Ty) with
      | [? (X : Type)] (M X):Type =u> M.ret (mexistT _ mBase X)
      | [? (X : Type) (F : forall x:X, Type)] forall (x : X), F x =u>
        \nu x : X,
          let T' := reduce (RedOneStep [rl:RedBeta]) (F x) in
          ''(mexistT _ n T) <- f T';
          n' <- M.abs_fun x n;
          T' <- (M.coerce (B:=MTele_Ty (n' x)) T >>= M.abs_fun x);
          M.ret (mexistT _ (mTele n') T')
      end) T.
*)

(* Try to check what is actually done by MTele_of' *)
(* Given a regular Coq Type T, return an MTele that represents the dependencies of T, an MTele_Ty mT of this telescope and a proof that T is equivalent to MFA mT *)
(* This means T already has all the dependencies intended and can be expressed though an MFA. Specifically this function is to be applied to something like: forall x..z, M (T x..z) because that is a type that can be represented in an MFA'ish manner *)
(* That also explains why only two cases are defined *)
Definition MTele_of' (T : Type) : M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } }:=
  (mfix1 f (T : Type) : M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } } :=
  mmatch T as T0 return M { m : MTele & { mT : MTele_Ty m & T =m= MFA mT } } with
  | [?X : Type] (M X):Type =u> [H]
    ret (existT (fun m => {mT : MTele_Ty m & T =m= MFA mT}) (mBase)
        (existT (fun mT : MTele_Ty mBase => T =m= MFA mT) _ H))
  | [?(X : Type) (F : forall x:X, Type)] (forall x:X, F x) =c> [H]
    \nu x,
      ''(existT _ m (existT _ mT E)) <- f (F x);
      m' <- abs_fun x m;
      mT' <- (coerce mT >>= abs_fun (P:=fun x => MTele_Ty (m' x)) x);
      E' <- coerce (@meq_refl _ (MFA (n:=mTele m') mT'));
      ret (existT _ (mTele m') (existT _ mT' E'))
  end) T.

Definition test_mteleof := fun (Y : Type) (X : Y -> Type) (y : Y) => ltac:(mrun (MTele_of' (M (X y)))).
Eval cbn in test_mteleof.

(* I should raise exceptions when something's wrong *)
(*
Definition MTele_of (A : Type) (B : Type -> Type)
  (succ : forall (n : MTele) (A' : MTele_Ty n), M (B (MTele_val A'))) :
  M (B A) :=
  (mfix1 rec (T : Type) : M (B T) :=
     mmatch T as T' return M (B T') with
     | [? (X : Type)] (M X):Type =>
       succ mBase (M X)
     | [? (X : Type) (R : X -> Type)] forall (x : X), R x =>
       \nu x : X,
         mmatch B (R x) return M (B (forall (x : X), R x)) with
         | [? (n : MTele) (A' : MTele_Ty n)] B (@MTele_val SType n A') =>
           nA <- abs_fun x A';
           succ (mTele (fun x : X => n)) nA
         end 
         (* succ (mTele (fun _ : X => _)) (fun x : X => r) *)
     end
  ) A.
*)

Definition MTele_of (A : Type) (B : Type -> Type)
  (ok : forall (n : MTele) (A' : MTele_Ty n), M (B (MFA A'))) : M (B A) :=
  ''(existT _ n (existT _ mT E)) <- MTele_of' A;
  match meq_sym E in _ =m= R return M (B R) with
  | meq_refl => 
    ok n mT
  end.

(*
Definition MMTele_of (A : Type) (nB : Type -> MTele) (B : forall A' : Type, MTele_Ty (nB A))
  (ok : forall (n : MTele) (A' : MTele_Ty n), MFA (B (MFA A'))) : MFA (B A) :=
  ''(existT _ n (existT _ mT E)) <- MTele_of' A;
  match meq_sym E in _ =m= R return MFA (B R) with
  | meq_refl => 
    ok n mT
  end.
*)

Class BLA (A : Type) (a : A) (bla_t : Type) := Bla { bla_v : bla_t }.

Definition NotSameType : Exception. exact exception. Qed.

(*
Definition to_tree_eq A : M m:{T: TyTree & A =m= to_ty T} :=
  T <- to_tree A;
  r <- unify_or_fail UniCoq A (to_ty T);
  ret (mexistT _ T r).

Obligation Tactic := intros.

Program Definition bla A (a: A) (A' : TyTree) (teq : A =m= to_ty A'):=
  (* ''(mexistT _ A' teq) <- to_tree_eq A; *)
  ret (mexistT _ A' (@lift' A' _)).
Next Obligation.
  rewrite <- teq.
  exact a.
Defined.

Program Definition myhint (A : Type) (a : A) (R : Type) : M (BLA A a R):=
  print "myhint is running";;
  ''(existT _ n _) <- (MTele_of' R);
  ''(mexistT _ A' teq) <- to_tree_eq A;
  bla _ a A' teq.
 
  (* match meq_sym teq in _ =m= T return forall a : T, M (BLA T a R) with *)
  (* | meq_refl => fun a' : (to_ty A') => *)
  (*     (* let pack := mexistT to_ty A' v in *) *)
  (*     ''(mexistT _ T' t') <- @lift' A' _ n; *)
  (*     (* ret (Bla A a (to_ty A') v) *) *)
  (*     ret _(* (Bla (to_ty A') a' (to_ty T) t) *) *)
  (* end a. *)
Next Obligation.
Set Printing Universes.
  refine (''(mexistT _ T t) <- @lift' A' _ n; _).
  
  (* ''(existT _ T v) <- lift' a n; *)
  (* ret (Bla A a (to_ty T) v). *)
  (* ''(existT _ T v) <- lift' a n; *)
  (* ret v. *)
*)

Definition to_tree_eq A : M m:{T: TyTree & _} :=
  T <- to_tree A;
  r <- unify_univ A (to_ty T) UniCoq;
  match r with mSome f => ret (mexistT _ T f) | mNone => failwith "pumba" end.

Obligation Tactic := intros.

Definition myhint (A : Type) (a : A) (R : Type) : M (BLA A a R):=
  mtry
  print "myhint is running";;
  M.dbg_term "R: " R;;
  M.dbg_term "A: " A;;
  ''(existT _ n _) <- (MTele_of' R);
  M.dbg_term "n: " n;;
  ''(mexistT _ A' f) <- to_tree_eq A;
  M.dbg_term "f: " f;;
  ''(mexistT _ T t) <- @lift' A' (f a) n;
  M.dbg_term "T: " T;;
  M.dbg_term "t: " t;;
  r <- unify R (to_ty T) UniCoq;
  match r with
  | mNone => raise NotSameType
  | mSome eq =>
    match meq_sym eq in _ =m= R' return forall r : to_ty T, M (BLA A a R') with
    | meq_refl => fun t' =>
      ret (Bla A a (to_ty T) t')
    end t
  end
  with [? e] e => dbg_term "fallo por: " e;; raise e end.



Hint Extern 0 (@BLA ?A ?a ?R) => mrun (myhint A a R) : typeclass_instances.

Notation "'mlift' f" :=
  (
    @bla_v _ f _ _
  ) (at level 90,
     format "mlift f").

Definition test3 : nat -> M nat := mlift (@print_term nat). 