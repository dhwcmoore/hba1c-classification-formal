Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope Q_scope.
Local Open Scope string_scope.


Definition interval (A : Type) := (A * option A)%type.

Definition in_interval (x : Q) (i : interval Q) : bool :=
  let (l, ro) := i in
  Qle_bool l x &&
  match ro with
  | Some r => negb (Qle_bool r x)
  | None => true
  end.

Definition make_classifier (bounds : list (interval Q * string)) :=
  fun x =>
    match find (fun '(i, _) => in_interval x i) bounds with
    | Some (_, label) => label
    | None => "Unknown"%string
    end.



Definition valid_classifier (bounds : list (interval Q * string)) : Prop :=
  True.

