From Mtac2 Require Import Base MTele Mtac2.
Import Sorts.S.
Import M.notations.
Import M.M.

Goal Type.
 mrun (\nu f : unit -> Type,
         \nu g : (forall (u : unit) , f u),
           let F := f tt in
           F <- abs_fun (P := fun _ => Type) g F;
           F <- @abs_fun _ (fun f => (forall (u : unit) , f u) -> Type) f F;
           ret (F (fun a => unit) (fun a => tt))).

Goal Type.
 Mtac Do Unset_Trace.
 mrun (\nu f : forall (s : Sort), s,
         \nu g : (forall (s: Sort), f s),
           let F := f SType in
           F <- abs_fun (P := fun _ => Type) g F;
           F <- @abs_fun _ (fun f => (forall (s: Sort), f s) -> Type) f F;
           ret (F (fun a => _) (fun a => _))).

Goal Type.
 mrun (\nu f : forall (s : Sort), MTele_Sort s mBase -> s,
         \nu g : (forall (s: Sort) (T : MTele_Sort s mBase), MTele_val T -> f s T),
           let F := f SType unit in
           F <- abs_fun (P := fun _ => Type) g F;
           F <- abs_fun (P := fun f => (forall (s: Sort) (T : MTele_Sort s mBase), MTele_val T -> f s T) -> Type) f F;
           ret (F (fun a b => a) (fun a b c => b))).