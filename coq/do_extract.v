(* coq/do_extract.v *)

From Stdlib Require Import String.
From Rocq Require Import IntervalClassifier.
From Rocq Require Import coq_hba1c.

Extraction Language OCaml.

Extraction "ocaml/hba1c_classifier.ml" make_classifier.
