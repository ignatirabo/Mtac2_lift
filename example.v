From Mtac2 Require Import Mtac2 meta.MTeleMatch meta.MFix.

Definition max (S: Set) : M (S -> S -> S) :=
  mmatch S in Set as S' return M (S' -> S' -> S') with
  | nat => M.ret Nat.max
  end.

Set Use Unicoq.
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
Definition list_max (S: Set)  :=
  max <- max S; (* error, the types clearly do not allow this *)
  (* the mfix has tipe forall ... *)
  (* with l_bind it should be possible? *)
  mfix f (l: list S) : l' <> nil -> M S :=
    mtmmatch l as l' return l' <> nil -> M S with
    | [? e] [e] =m> fun nonE=>M.ret e
    | [? e1 e2 l'] (e1 :: e2 :: l') =m> fun nonE =>
      m <- max e1 e2;
      f (m :: l') cons_not_nil
    end.
