From Coq Require Import QArith.QArith.
From Coq Require Import Strings.String.
From Coq Require Import Extraction.
From Rocq Require Import IntervalClassifier.
From Rocq Require Import coq_hba1c.

Extraction Language OCaml.

Extraction "ocaml/hba1c_classifier.ml" classify_hba1c.
