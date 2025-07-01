Require Import Coq.QArith.QArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Rocq.IntervalClassifier.
Import ListNotations.

Open Scope Q_scope.
Local Open Scope string_scope.

Definition hba1c_bounds : list (interval Q * string) :=
  [ ((Qmake 57 10, Some (Qmake 65 10)), "Pre-Diabetes"%string)
  ; ((Qmake 65 10, Some (Qmake 100 10)), "Diabetes"%string)
  ].

Definition classify_hba1c := make_classifier hba1c_bounds.
