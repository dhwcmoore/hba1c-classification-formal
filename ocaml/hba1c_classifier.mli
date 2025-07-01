
type bool =
| True
| False

val negb : bool -> bool

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Z :
 sig
  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool
 end

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

type q = { qnum : z; qden : positive }

val qle_bool : q -> q -> bool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

type 'a interval = ('a, 'a option) prod

val in_interval : q -> q interval -> bool

val make_classifier : (q interval, string) prod list -> q -> string

val hba1c_bounds : (q interval, string) prod list

val classify_hba1c : q -> string
