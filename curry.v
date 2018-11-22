From Mtac2 Require Import Base Mtac2 Sorts MTele.
Import Sorts.S.
Import M.notations.
Import M.M.

Local Notation MFA T := (MTele_val (MTele_C SType SProp M T)).

(* If recursion is needed then it's TyTree, if not only Type *)
Inductive TyTree : Type :=
| tyTree_M (p : bool) (T : Type) : TyTree
| tyTree_imp (p : bool) (T R : TyTree) : TyTree
| tyTree_FATele (P : bool) {m : MTele} (T : MTele_Ty m) (F : forall t : MTele_val T, TyTree) : TyTree  
| tyTree_FA (p : bool) (T : Type) (F : T -> TyTree) : TyTree
| tyTree_FAType (p : bool) (F : Type -> Type) : TyTree
| tyTree_ow (p : bool) (T : Type) : TyTree
.

Fixpoint tree_ty (X : TyTree) : Type :=
  match X as X' with
  | tyTree_M _ T => M T
  | tyTree_imp _ T R => tree_ty T -> tree_ty R
  | @tyTree_FATele _ m T F => forall T, tree_ty (F T)
  | tyTree_FA _ T F => forall t : T, tree_ty (F t)
  | tyTree_FAType _ F => forall T : Type, F T 
  | tyTree_ow _ T => T
  end.

Definition ty_tree (X : Type) : M TyTree :=
  (mfix2 rec (X : Type) (p : bool) : M TyTree :=
    mmatch X as X return M TyTree with
    | [? T : Type] (M T):Type =>
      ret (tyTree_M p T)
    | [? T R : Type] T -> R =>
      T <- rec T (negb p);
      R <- rec R p;
      ret (tyTree_imp p T R) 
    | [? (m : MTele) (T : MTele_Ty m) (F : forall x : MTele_val T, Type)] forall T , F T =>
      \nu t : _,
        F <- rec (F t) p;
        F <- abs_fun t F;
        ret (tyTree_FATele p T F)  
    | [? T (F : forall t : T, Type)] forall t : T, F t =>
      \nu t : T,
        F <- rec (F t) p;
        F <- abs_fun t F; (* Maybe abs_prod_type ? *)
        ret (tyTree_FA p T F)
    | [? F : Type -> Type] forall T : Type, F T =>
      ret (tyTree_FAType p F)
    | _ => ret (tyTree_ow p X) 
    end) X true.

Definition ty_tree' {X : Type} (x : X) := ty_tree X.

Goal M TyTree.
mrun (ty_tree' (@bind)).
w